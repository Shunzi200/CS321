#lang plai
(print-only-errors)


#|
<SFAE> = <num>
| {+ <SFAE> <SFAE>}
| {- <SFAE> <SFAE>}
| {fun {<id>} <SFAE>}
| {<SFAE> <SFAE>} ;; function application
| <id>
| {struct {<id> <SFAE>}*} ;; all fields must be distinct
| {get <SFAE> <id>}
| {set <SFAE> <id> <SFAE>}
| {seqn <SFAE> <SFAE>}
|#

(define-type SFAE
  [num (n number?)]
  [add (lhs SFAE?)
       (rhs SFAE?)]
  [sub (lhs SFAE?)
       (rhs SFAE?)]
  [fun (param-name symbol?)
       (body SFAE?)]
  [app (fun-expr SFAE?)
       (arg-expr SFAE?)]
  [id (name symbol?)]
  [S-struct (structElem (listof (list/c SFAE? SFAE?)))]
  [S-get (structure SFAE?)
         (elemID SFAE?)]
  [S-set (expr1 SFAE?)
         (elemID SFAE?)
         (expr2 SFAE?)]
  [seqn (expr1 SFAE?)
        (expr2 SFAE?)])


(define-type Store
  [mtSto]
  [aSto (address integer?)
        (value SFAE-Value?)
        (rest Store?)])

(define-type Value*Store
  [v*s (v SFAE-Value?)
       (s Store?)])

(define-type SFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body SFAE?)
            (ds DefSub?)]
  [boxV (address integer?)]
  [structureV (structureObj (listof (list/c SFAE? number?)))]
  )

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value SFAE-Value?)
         (rest DefSub?)])

;;------------------------------------------
;; interp-expr : SFAE -> number 'struct or 'function
(define (interp-expr an-fae)
  (let* ([result (interp an-fae (mtSub) (mtSto))])
    (type-case Value*Store result
      [v*s (init-val st2)
           (type-case SFAE-Value init-val
             [numV (n) n]
             [closureV (param-name body closed-ds) 'function]
             [boxV (address) 'box]
             [structureV (structureObj) 'struct]
             )])))


;; interp-two : BFAE? BFAE? DefSub? Store?
;;              (BFAE-Value? BFAE-Value? Store? -> Value*Store?)
;;              -> Value*Store?
(define (interp-two e1 e2 ds st finish)
  (type-case Value*Store (interp e1 ds st)
    [v*s (v1 st2)
         (type-case Value*Store (interp e2 ds st2)
           [v*s (v2 st3)
                (finish v1 v2 st3)])]))


;; interp-twoStruct : BFAE? BFAE? DefSub? Store?
;;              (BFAE-Value? BFAE-Value? Store? -> Value*Store?)
;;              -> Value*Store?
(define (interp-twoStruct e1 e2 ds st finish)
  (type-case Value*Store e1
    [v*s (v1 st2)
         (type-case Value*Store  e2
           [v*s (v2 st3)
                (finish v1 v2 st3)])]))

;; lookup-store : integer? Store -> SFAE-Value?
(define (lookup-store a s)
  (type-case Store s
    [mtSto () (error 'interp "internal error: dangling pointer ~a" s)]
    [aSto (a2 v r)
          (if (= a a2) v (lookup-store a r))]))

;; malloc : Store? -> integer?
(define (malloc st)
  (+ 1 (max-address st)))


(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (a v r) (max a (max-address r))]))

;; numop : (number? number? -> number?)
;;         BFAE? BFAE? DefSub? Store? -> Value*Store?
(define (numop op l r ds st)
  (interp-two
   l r ds st
   (lambda (l-val r-val st3)
     (unless (numV? l-val)
       (error 'interp "expected number, got ~a" l-val))
     (unless (numV? r-val)
       (error 'interp "expected number, got ~a" r-val))
     (v*s (numV (op (numV-n l-val) (numV-n r-val)))
          st3))))


;; lookup : symbol? DefSub? -> SFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))
;;------------------------------------------
;;New Helpers

(define (createBox sID sVal ds st)
  (define address (malloc st))
  (list  address (v*s (boxV address) 
                      (aSto address sVal st))))


(define (helperAddToStore sID sVal ds st)
  (type-case Value*Store sVal
    [v*s (init-val st2)
         (let ([result (createBox sID init-val ds st)])
           (list (list sID (first result)) (second result))
           )
         ]))

(define (helperConcatenate structureObj structureList ds finalStore)
  (if (null? structureObj)
      (list structureList finalStore)
    
      (let ([result (helperAddToStore (first (first structureObj)) (interp (second (first structureObj)) ds finalStore) ds finalStore)])
        (type-case Value*Store (second result)
          [v*s (init-val st2)
               (helperConcatenate (rest structureObj) (cons (first result) structureList ) ds st2)
               ])
        )
        
      )
  )

(define (helperSetStructureAddress structAddress newStruct st)
  (aSto structAddress (structureV newStruct) st))

(define (helperGetStructureAddress structAddress st)
  (type-case SFAE-Value (lookup-store structAddress st)
    [structureV (structureList) structureList]
    [else (error 'interp (format "expected struct, but found ~a at address ~a" (lookup-store structAddress st) structAddress))]
    ))

(define (findMatchingBox sID structureObj)
  (if (null? structureObj)
      (error 'interp "unknown field")
      (if (equal? sID (first (first structureObj)))
          (second (first structureObj))
          (findMatchingBox sID (rest structureObj))
          )
      )      
  )

(define (helperOpenBox address ds st)
  (v*s (lookup-store address st)
       st)
  )

(define (helperReturnGet sID structureObj ds st)
  (type-case Value*Store structureObj
    [v*s (struct-address-val st2)
         (unless (boxV? struct-address-val)
           (error 'interp "expected box address"))
         (define address (boxV-address struct-address-val))
         (let ([structureList (helperGetStructureAddress address st2)])
           structureList
           (let ([foundAddress (findMatchingBox sID structureList)])
             (helperOpenBox foundAddress ds st2)
             ))])
  )



(define (helperSetBox address newVal ds st newStore)
  (type-case Store st
    [aSto (currAdd currVal st2)
          (if (equal? address currAdd)
              (helperSetBox address newVal ds st2 (aSto currAdd newVal newStore))
              (helperSetBox address newVal ds st2 (aSto currAdd currVal newStore))
              )
          ]
    [else 
     newStore
     ]
    )

  )
  
(define (helperReturnSet sID structureObj expr2 ds st)
  (type-case Value*Store structureObj
    [v*s (struct-address-val st2)
         (unless (boxV? struct-address-val)
           (error 'interp "expected box address"))
         (define address (boxV-address struct-address-val))
         (let* ([structureList (helperGetStructureAddress address st2)]
                [oldBoxValue (helperOpenBox (findMatchingBox sID structureList) ds st2)]
                [fieldAddress (findMatchingBox sID structureList)])
           (type-case Value*Store (interp expr2 ds st2)
             [v*s (new-value st3)
                  (v*s (v*s-v oldBoxValue) 
                       (helperSetBox fieldAddress new-value ds st (mtSto)))
                   
                  ]
             ))
         ]
    ))
                
;;(helperSetStructureAddress address (helperBuildNew sID structureList updatedVS '()) st2)))]))



; size : any -> number?
; computes a (very rough!) approximation of
; the size a PLAI object takes in memory
(define (size s)
  (cond
    [(struct? s)
     (size (struct->vector s))]
    [(vector? s)
     (for/fold ([tot 0])
               ([ele (in-vector s)])
       (+ tot (size ele)))]
    [(pair? s)
     (+ 1 (size (car s)) (size (cdr s)))]
    [else 1]))

;; ----------------------------------------------------------------------
;; interp-test : s-expression -> SFAE-Value?
(define (interp-test s-exp)
  (v*s-v (interp (parse s-exp) (mtSub) (mtSto))))

;; interp : SFAE? DefSub? Store? -> Value*Store?
(define (interp a-sfae ds st) ; NEW
 ;;(printf "size ~a\n" (size st))
  ;; (displayln "Struct")
  ;;(displayln st)
  (type-case SFAE a-sfae
    [num (n) (v*s (numV n)
                  st)]
    [add (l r) (numop + l r ds st)]
    [sub (l r) (numop - l r ds st)]
    
    [id (name)
        (v*s (lookup name ds)
             st)]
    [fun (param-name body)
         (v*s (closureV param-name body ds)
              st)]
    [app (fun-expr arg-expr)
         (interp-two fun-expr arg-expr ds st
                     (lambda (fun-val arg-val st3)
                       (unless (closureV? fun-val)
                         (error 'interp "expected function"))
                       (interp (closureV-body fun-val)
                               (aSub (closureV-param-name fun-val)
                                     arg-val
                                     (closureV-ds fun-val))
                               st3)))]

    [S-struct (structureObj)
              (let ([result 
                     (helperConcatenate structureObj '() ds st)])
                (define structAddress (malloc (second result)))
                (v*s (boxV structAddress) 
                     (aSto structAddress (structureV (first result)) (second result)))
                )  
              ]

    [S-get (structureObj eID)
           
           (helperReturnGet eID (interp structureObj ds st) ds st)
        
           ]

    [S-set (structureObj eID expr2)
           
           (helperReturnSet eID (interp structureObj ds st) expr2 ds st)
    
           ]

 
    [seqn (expr1 expr2)
          (interp-two expr1 expr2 ds st
                      (lambda (v1 v2 st3)
                        (v*s v2 st3)))]))


;; ----------------------------------------------------------------------
;; parse : s-expression -> SFAE?
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid SFAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp "add" 3)
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp "sub" 3)
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(fun)
            (check-pieces s-exp "fun" 3)
            (check-pieces (second s-exp) "parameter list" 1)
            (fun (first (second s-exp))
                 (parse (third s-exp)))]
           [(struct)
            (unless (distinct? '() (rest s-exp))
              (error "Duplicate field in struct"))
            (S-struct (map (lambda (field)
                             (list (parse (first field))
                                   (parse (second field)))) 
                           (rest s-exp)))]
           [(get)
            (check-pieces s-exp "get" 3)
            (S-get (parse (second s-exp))
                   (parse (third s-exp)))]
           [(set)
            (check-pieces s-exp "set" 4)
            (S-set (parse (second s-exp))
                   (parse (third s-exp))
                   (parse (fourth s-exp)))]
           [(seqn)
            (check-pieces s-exp "seqn" 3)
            (seqn (parse (second s-exp))
                  (parse (third s-exp)))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "expected SFAE got ~a" s-exp)]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

(define (distinct? seen-fields structure)
  (if (null? structure)
      #t
      (let ([field-name (first (first structure))]) 
        (if (member field-name seen-fields)
            #f
            (distinct? (cons field-name seen-fields) (rest structure))))))


;;
;; 5 -> 5
(test (interp-test `5)
      (numV 5))
;; {+ 1 2} -> 3
(test (interp-test `{+ 1 2})
      (numV 3))
;; {- 3 4} -> -1
(test (interp-test `{- 3 4})
      (numV -1))
;; {+ {+ 1 2} {- 3 4}} -> 2
(test (interp-test `{+ {+ 1 2} {- 3 4}})
      (numV 2))
(test (interp-expr (parse `{+ {+ 1 2} {- 3 4}}))
      2)
(test (parse '{struct {x 1}})
      (S-struct (list (list (id 'x) (num 1)))))

(test (parse '{struct {x 1} {y 2}})
      (S-struct (list (list (id 'x) (num 1)) (list (id 'y) (num 2)))))

(test/exn (parse '{struct {x 1} {x 2}})
          "Duplicate field in struct")

(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
          "unknown field")

(test (interp-expr (parse `{get {struct {x 1} {y 10}} x}))
      1)

(test (interp-expr (parse `{get {struct {x 1} {y 10}} y}))
      10)

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {struct {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {get r z}}
                            {struct {x 1} {z 8}}}))
      8)

(test (interp-expr (parse '{{fun {r}
                                 {get r z}}
                            {struct {x 1} {z {+ 2 6}}}}))
      8)


(test (interp-expr (parse '{set {struct {x 42}} x 2}))
      42)


(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {struct {x 1}}}))
      5)


(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}} ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}} ; r1
                            {struct {a 3} {b 4}}})) ; r2
      5)


(test (interp-expr (app
                    (fun
                     'r1
                     (add
                      (S-get (id 'r1) (id 'b))
                      (S-get (id 'r1) (id 'a))))
                    (S-struct
                     (list
                      (list (id 'a) (num 1))
                      (list (id 'b) (num 2))))))
      3)

(test (interp-expr (parse '{{fun {r1}
                                 {+     
                                  {get r1 b}
                                  {get r1 a}}
                              
                              
                                  
                                 }
                            {struct {a 1} {b 2}}
                            }
                          ))
      3)


(test (interp-expr (parse '{{fun {r} {seqn {set r x {get r y}} {get r x}}} {struct {x 10} {y 7}} }
                          ))
      7)

#|
(interp-expr (parse `{{fun {b} {{fun {f} {f f}}
{fun {f} {seqn {set b x 2}
{f f}}}}}
{struct {x 1}}}))
|#
