#lang plai/gc2/collector

(print-only-errors)

#|
heap:    | 'free | 'free | 'free | ...                          NEW!
flat:    ... | 'flat | <payload>   | ...
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
closure: ... | 'clos | <code-ptr> | <n-free-vars> | <fv0> | <fv1> | ... | ...  
|#


;;-------------
;;allocation-ptr is at index 0
;;active-space at index 1
;;left at index 2
;;right at index 3

(define (update-state address value)
  (heap-set! address value)
  )

(define (get-allocation)
  (heap-ref 0)
  )

(define (get-active-space)
  (heap-ref 1)
  )
(define (get-left)
  (heap-ref 2)
  )

(define (get-right)
  (heap-ref 3)
  )

(define (half-point)
  (+ (/ (- (heap-size) 4) 2) 4)
  )
(define (get-cons-p1 start)
  (heap-ref (+ start 1))
  )
(define (get-cons-p2 start)
  (heap-ref (+ start 2))
  )
(define (get-clos-pi start i)
  (heap-ref (+ start 3 i))
  )

(define (get-clos-name start)
  (heap-ref (+ start 1))
  )


(define (get-clos-n start)
  (heap-ref (+ start 2))
  )

(define (get-pointer-p start)
  (heap-ref (+ start 1))
  )

(define (init-allocator)
  (for ([i (in-range (heap-size))])
    (heap-set! i 'free))
  (update-state 0 4)
  (update-state 1 0)
  (update-state 2 (half-point))
  (update-state 3 (half-point))
  )

(define (switch-active-space)
  (if (equal? (get-active-space) 0)
      (update-state 1 1)
      (update-state 1 0)
      )
  )
(define (switch-allocation-ptr)
  ;; (if (equal? (get-active-space) 0)
  ;;(update-state 0 4)
  ;; (update-state 0 (half-point))
  ;; )
  (update-state 0 (get-right))
  
  )
(define (reset-pointers)
  (if (equal? (get-active-space) 0)
      (begin
        (update-state 2 (half-point))
        (update-state 3 (half-point)))
      (begin
        (update-state 2 4)
        (update-state 3 4))))



;; find-free-space : int? int? -> (or/c location false?)
(define (find-free-spaces n)
  (if (equal? (get-active-space) 0)
      (if (or (>= (+ (get-allocation) n) (half-point)) (>= (+ (get-allocation) n) (heap-size)))
          #f
          (begin
            (let ([holderAlloc (get-allocation)])
              (update-state 0 (+ (get-allocation) n))
              holderAlloc)
            )
          )
      
      (if (or (< (+ (get-allocation) n) (half-point)) (>= (+ (get-allocation) n) (heap-size)))
          #f
          (begin
            (let ([holderAlloc (get-allocation)])
              (update-state 0 (+ (get-allocation) n))
              holderAlloc)
            ))
      )
  )

;; malloc : size -> address
(define (malloc n root1 root2)
  ;;(collect-garbage root1 root2)
  (define a (find-free-spaces n))
  (cond [(integer? a)
         a]
        [else
         (collect-garbage root1 root2)
         (define a (find-free-spaces n))
         (cond [(integer? a)
                a]
               [else
                (error 'malloc "out of memory for space ~a" (get-active-space))])]))
#|
(define (collect-garbage root1 root2)
  (displayln "starting gc")
  (read-line)
  (displayln "validate heap")
  (validate-heap (get-allocation))
  (read-line)
  (displayln "traverse roots")
 (traverse/roots (get-root-set))
 
  (read-line)
  (displayln "traverse root1")
  (traverse/roots root1)
  (read-line)
  (displayln "traverse root2")
  (traverse/roots root2)
  (read-line)
  (displayln "traverse queue")
  (traverse/queue)
  (read-line)
  (displayln "validate heap")
  (validate-heap (get-allocation))
    (displayln "switch space")
  (read-line)
  (switch-active-space)

    (displayln "switch allocation")
  (read-line)
  (switch-allocation-ptr)
 
  (read-line)
  (reset-pointers)
  
  )

|#
(define (collect-garbage root1 root2)
  (validate-heap (get-allocation))
  (traverse/roots (get-root-set))
  (traverse/roots root1)
  (traverse/roots root2)
  (traverse/queue)
  (validate-heap (get-allocation))
  (switch-active-space)
  (switch-allocation-ptr)
  (reset-pointers)
  )


(define (traverse/roots roots)
  (cond [(false? roots)
         (void)]
        [(list? roots)
         (for ([r (in-list roots)])
           (let ([newPointer
                  (traverse/loc (read-root r))])
             (set-root! r newPointer))
           )]
        [(root? roots)
         (let ([newPointer (traverse/loc (read-root roots))])
           (set-root! roots newPointer))
         ]
        [else
         (error 'traverse/roots "unexpected root: ~a" roots)]))

(define (validate-pointer a)
  (define ptr (heap-ref a))
  (unless (and (integer? ptr)
               (ptr . >= . 4)
               (ptr . < . (heap-size))
               ;;(member (heap-ref ptr) '(flat cons clos pointer))
               )
    (error 'validate-pointer "invalid pointer @ ~a ~a" a (heap-ref a))))

(define (validate-heap start)
  (if (equal? (get-active-space) 0)
      (unless (or (>= start (half-point)) (>= start (heap-size)))
        (case (heap-ref start)
          [(flat) (validate-heap (+ start 2))]
          [(cons) (validate-pointer (+ start 1))
                  (validate-pointer (+ start 2))
                  (validate-heap (+ start 3))]
          [(clos) (for ([i (in-range (heap-ref (+ start 2)))])
                    (validate-pointer (+ start 3 i)))
                  (validate-heap (+ start 3 (heap-ref (+ start 2))))]
          [(free) (validate-heap (+ start 1))]
          [(pointer) (validate-heap (+ start 2))]
          [else (validate-heap (+ start 2))]))
      (unless (or (< start (half-point)) (>= start (heap-size)))
        (case (heap-ref start)
          [(flat) (validate-heap (+ start 2))]
          [(cons) (validate-pointer (+ start 1))
                  (validate-pointer (+ start 2))
                  (validate-heap (+ start 3))]
          [(clos) (for ([i (in-range (heap-ref (+ start 2)))])
                    (validate-pointer (+ start 3 i)))
                  (validate-heap (+ start 3 (heap-ref (+ start 2))))]
          [(free) (validate-heap (+ start 1))]
          [(pointer) (validate-heap (+ start 2))]
          [else (validate-heap (+ start 2))]
          ))))

(define (traverse/loc ptr)
  (let ([right-holder (get-right)])
    (case (heap-ref ptr)
      [(flat)
       (heap-set! (get-right) 'flat)
       (heap-set! (+ (get-right) 1) (heap-ref (+ ptr 1)))
       (heap-set! ptr 'pointer)
       (heap-set! (+ ptr 1) (get-right))
       (update-state 3 (+ (get-right) 2))
       right-holder
       ]
      [(cons)
       (heap-set! (get-right) 'cons)
       (heap-set! (+ (get-right) 1) (get-cons-p1 ptr))
       (heap-set! (+ (get-right) 2) (get-cons-p2 ptr))
       (heap-set! ptr 'pointer)
       (heap-set! (+ 1 ptr) (get-right))
       (update-state 3 (+ (get-right) 3))
       right-holder
       ]
      [(clos)
       (heap-set! (get-right) 'clos)
       (heap-set! (+ (get-right) 1) (get-clos-name ptr))
       (heap-set! (+ (get-right) 2) (get-clos-n ptr))
     
       (heap-set! ptr 'pointer)
       (heap-set! (+ ptr 1) (get-right))
     
       (let ([n-free  (get-clos-n ptr)])
       
         (for ([i (in-range 0 n-free)])
           (heap-set! (+ (get-right) 3 i) (get-clos-pi ptr i))
           )

         (update-state 3 (+ (get-right) 3 n-free))
         )
       right-holder
       ]
      ['pointer
       (heap-ref (+ ptr 1))]
      [(free) (error 'traverse/loc "traverse/loc dangling pointer!")]
      [else (error 'traverse/loc "traverse/loc unexpected tag @ ~a" ptr)]))
  )

(define (traverse/queue)
  (if (>= (get-left) (get-right))
      (void)
      (case (heap-ref (get-left))
        [(flat) 
         (update-state 2 (+ (get-left) 2))
         (traverse/queue)
         ]
        [(cons)
         (case (heap-ref (get-cons-p1 (get-left)))
           [(pointer)
            (let ([currRight  (traverse/loc (get-cons-p1 (get-left)))])
              (heap-set! (+ (get-left) 1) currRight)
              )
            ]
           [else
            (let ([currRight (traverse/loc (get-cons-p1 (get-left)))])
              (heap-set! (+ (get-left) 1) currRight)
              )]
           )
         (case (heap-ref (get-cons-p2 (get-left)))
           [(pointer)
            (let ([currRight (traverse/loc (get-cons-p2 (get-left)))])
              (heap-set! (+ (get-left) 2) currRight)
              )
            ]
           [else
            (let ([currRight (traverse/loc (get-cons-p2 (get-left)))])
              
              (heap-set! (+ (get-left) 2) currRight)
              )]
           )
         (update-state 2 (+ (get-left) 3))
         (traverse/queue)
         ]  
        [(clos)
         (let ([n-free (get-clos-n (get-left))])
           (for ([i (in-range 0 n-free)])
             (case (heap-ref (get-clos-pi (get-left) i))
               [(pointer)
                (let ([currRight (traverse/loc (get-clos-pi (get-left) i))])
                  (heap-set! (+ (get-left) 3 i) currRight)
                  )
                ]
               [else
                (let ([currRight (traverse/loc (get-clos-pi (get-left) i))])
                 
                  (heap-set! (+ (get-left) 3 i) currRight)
                  )]
               )
             )
           (update-state 2 (+ (get-left) n-free 3))
           (traverse/queue)

           )
         ]
        [(free) (error 'traverse/loc "traverse/queue dangling pointer!")]
        [else (error 'traverse/loc "traverse/queue unexpected tag @ ~a" (get-left))]

        )))



;; ----------------------------------------------------------------------

#|
flat:    ... | 'flat | <payload> | ...
|#
;; gc:alloc-flat : flat-value -> location
(define (gc:alloc-flat value)
  (define address (malloc 2 #f #f))
  (heap-set! address 'flat)
  (heap-set! (+ address 1) value)
  address)
;; gc:flat? : location -> boolean
(define (gc:flat? address)
  (equal? (heap-ref address) 'flat))
;; gc:deref : location -> flat-value
(define (gc:deref address)
  (unless (gc:flat? address)
    (error 'gc:deref "expected flat @ ~a" address))
  (heap-ref (+ address 1)))


#|
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
|#
;; gc:cons : root root -> location
(define (gc:cons root1 root2)
  (define address (malloc 3 root1 root2))
  (heap-set! address 'cons)
  (heap-set! (+ address 1) (read-root root1))
  (heap-set! (+ address 2) (read-root root2))
  address)
;; gc:cons? : location -> boolean
(define (gc:cons? address)
  (equal? (heap-ref address) 'cons))
;; gc:first : location -> location
(define (gc:first address)
  (unless (gc:cons? address)
    (error 'gc:first "expected cons @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:rest : location -> location
(define (gc:rest address)
  (unless (gc:cons? address)
    (error 'gc:rest "expected cons @ ~a" address))
  (heap-ref (+ address 2)))
;; gc:set-first! : location location -> void
(define (gc:set-first! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-first! "expected cons @ ~a" address))
  (heap-set! (+ address 1) new-value-address))
;; gc:set-rest! : location location -> void
(define (gc:set-rest! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-rest! "expected cons @ ~a" address))
  (heap-set! (+ address 2) new-value-address))


#|
closure: ... | 'clos | <code-ptr> | <n-free-vars> | <fv0> | <fv1> | ... | ...
|#
;; gc:closure : opaque-value (listof root) ->  location
(define (gc:closure code-ptr free-vars)
  (define address (malloc (+ 3 (length free-vars))
                          free-vars #f))
  (heap-set! address 'clos)
  (heap-set! (+ address 1) code-ptr)
  (heap-set! (+ address 2) (length free-vars))
  (for ([i  (in-range (length free-vars))]
        [fv (in-list free-vars)])
    (heap-set! (+ address 3 i) (read-root fv)))
  address)
;; gc:closure? :  location -> boolean
(define (gc:closure? address)
  (equal? (heap-ref address) 'clos))
;; gc:closure-code-ptr : location -> opaque-value
(define (gc:closure-code-ptr address)
  (unless (gc:closure? address)
    (error 'gc:closure-code-ptr "expected closure @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:closure-env-ref : location integer -> location
(define (gc:closure-env-ref address i)
  (unless (gc:closure? address)
    (error 'gc:closure-env-ref "expected closure @ ~a" address))
  (heap-ref (+ address 3 i)))
