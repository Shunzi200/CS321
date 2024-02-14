#lang plai

;;(print-only-errors)

(define-type Tree
  [positive-leaf (val natural?)]
  [negative-leaf (val natural?)]
  [interior-node (left Tree?) (right Tree?)])


(define (contains? aTree target) ;;contains?
  (type-case Tree aTree
    [positive-leaf (n) (equal? n target)]
    [negative-leaf (n) (equal?  (- n) target)]
    [interior-node (left right)
                   (or (contains? left target) (contains? right target))]
    )
  )

(define (smallest aTree) ;;smallest
  (type-case Tree aTree
    [positive-leaf (n) n]
    [negative-leaf (n) (- n)]
    [interior-node (left right)
                   (min (smallest left) (smallest right))]
    )
  )
(define (addTree aTree) ;;helper function
  (type-case Tree aTree
    [positive-leaf (n) n]
    [negative-leaf (n) (- n)]
    [interior-node (left right) 
                   (+ (addTree left) (addTree right))]
    )
  )

(define (balanced? aTree) ;;balanced?
  (type-case Tree aTree
    [positive-leaf (n) #t]
    [negative-leaf (n) #t]
    [interior-node (left right)  (= 0 (addTree aTree))]
    )
  )

(define (deep-balanced? aTree) ;;deep-balanced?
  (type-case Tree aTree
    [positive-leaf (n) #t]
    [negative-leaf (n) #t]
    [interior-node (left right) (and (= 0 (addTree aTree)) (deep-balanced? left) (deep-balanced? right)) ]
    )
  )

(define (negate aTree) ;;negate
  (type-case Tree aTree
    [positive-leaf (n) (negative-leaf n)]
    [negative-leaf (n) (positive-leaf n)]
    [interior-node (left right)
                   (interior-node (negate left) (negate right))]
    )
  )

(define (add aTree addOn) ;;add
  (type-case Tree aTree
    [positive-leaf (n) (if (positive? (+ n addOn))
                           (positive-leaf (+ n addOn))
                           (negative-leaf (abs (+ n addOn)))
                           )]
    
    [negative-leaf (n) (if (positive? (+ (- n) addOn))
                           (positive-leaf (+ (- n) addOn))
                           (negative-leaf (abs (+ (- n) addOn)))
                           )]
    [interior-node (left right)
                   (interior-node (add left addOn) (add right addOn))]
    )
  )

(define (positive-thinking aTree) ;;positive-thinking
  (type-case Tree aTree
    [positive-leaf (n) (positive-leaf n)]
    [negative-leaf (n) #f]
    [interior-node (left right)
                   (cond
                     ((and (eq? #f (positive-thinking left)) (eq? #f (positive-thinking right)))
                      #f)
                     ((eq? #f (positive-thinking left))
                      (positive-thinking right))
                     ((eq? #f (positive-thinking right))
                      (positive-thinking left))
                     (else (interior-node(positive-thinking left) (positive-thinking right))))]
    )

  )

;;contains? tests:
(test (contains? (positive-leaf 6) 6)
      #t)
(test (contains? (interior-node (interior-node (positive-leaf 5) (negative-leaf 4))
                                (positive-leaf 3))
                 -4)
      #t)
(test (contains? (interior-node (positive-leaf 5) (negative-leaf 7))
                 3)
      #f)
(test (contains? (interior-node (positive-leaf 5) (negative-leaf 0))
                 0)
      #t)
(test (contains? (interior-node (negative-leaf 5) 
                                (interior-node (negative-leaf 2) (negative-leaf 1)))
                 1)
      #f)
(test (contains? (interior-node (positive-leaf 3) (positive-leaf 3)) -3)
      #f)
(test (contains? (interior-node (interior-node (positive-leaf 1) (interior-node (positive-leaf 11100000000) (negative-leaf 9)))
                                (positive-leaf 5))
                 5)
      #t)
(test (contains? (interior-node (interior-node (positive-leaf 5) (interior-node (positive-leaf 11100000000) (negative-leaf 9)))
                                (negative-leaf 5))
                 -5)
      #t)
(test (contains? (interior-node (interior-node (negative-leaf 1) (negative-leaf 50000)) (interior-node (positive-leaf 10) (negative-leaf 100000000)))
                 -100000000)
      #t)


;;smallest tests:
(test (smallest (positive-leaf 3) )
      3)
(test (smallest (interior-node (positive-leaf 10) (positive-leaf 5)))
      5)
(test (smallest (interior-node (interior-node (positive-leaf 1) (positive-leaf 50000)) (interior-node (positive-leaf 10) (positive-leaf 5))))
      1)
(test (smallest (interior-node (interior-node (negative-leaf 1) (negative-leaf 50000)) (interior-node (positive-leaf 10) (negative-leaf 100000000))))
      -100000000)
(test (smallest (interior-node (positive-leaf 500000) (negative-leaf 50000)))
      -50000)
(test (smallest (interior-node (positive-leaf 0) (negative-leaf 0)))
      0)
(test (smallest (interior-node (negative-leaf 0) (interior-node (negative-leaf 5) (interior-node (positive-leaf 3) (interior-node (negative-leaf 10) (negative-leaf 1))))))
      -10)

;;balanced? tests:
(test (balanced? (positive-leaf 6))
      #t)
(test (balanced? (positive-leaf 0))
      #t)
(test (balanced? (interior-node (positive-leaf 4)  (negative-leaf 4)))
      #t)
(test (balanced? (interior-node (interior-node (positive-leaf 2) (negative-leaf 6)) (interior-node (negative-leaf 0) (negative-leaf 9))))
      #f)
(test (balanced? (interior-node (positive-leaf 0) (negative-leaf 0)))
      #t)

(test (balanced? (interior-node (positive-leaf 5) (negative-leaf 5)))
      #t)

(test (balanced? (interior-node (positive-leaf 5) (interior-node (positive-leaf 5) (interior-node (positive-leaf 5) (interior-node (negative-leaf 10) (negative-leaf 5))))))
      #t)

(test (balanced? (interior-node (positive-leaf 0) (negative-leaf 5)))
      #f)

;;deep-balanced? tests:
(test (deep-balanced? (positive-leaf 6))
      #t)
(test (deep-balanced? (positive-leaf 0))
      #t)
(test (deep-balanced? (interior-node (positive-leaf 6)  (negative-leaf 6)))
      #t)
(test (deep-balanced? (interior-node (positive-leaf 4)  (negative-leaf 4)))
      #t)
(test (deep-balanced? (interior-node (positive-leaf 1)  (negative-leaf 4)))
      #f)
(test (deep-balanced? (interior-node (interior-node (positive-leaf 4)  (negative-leaf 3)) (interior-node (positive-leaf 2)  (negative-leaf 3))))
      #f)
(test (deep-balanced? (interior-node (interior-node (positive-leaf 4)  (negative-leaf 4)) (interior-node (positive-leaf 3)  (negative-leaf 3))))
      #t)

;;negate tests:
(test (negate (positive-leaf 6))
      (negative-leaf 6))
(test (negate (interior-node (positive-leaf 1) (positive-leaf 2)))
      (interior-node (negative-leaf 1) (negative-leaf 2))
      )
(test (negate (interior-node (positive-leaf 1) (negative-leaf 3)))
      (interior-node (negative-leaf 1) (positive-leaf 3))
      )

(test (negate (interior-node (interior-node (negative-leaf 0) (negative-leaf 3)) (positive-leaf 10)))
      (interior-node (interior-node (positive-leaf 0) (positive-leaf 3)) (negative-leaf 10))
      )

(test (negate (interior-node (interior-node (negative-leaf 0) (negative-leaf 3)) (positive-leaf 10)))
      (interior-node (interior-node (positive-leaf 0) (positive-leaf 3)) (negative-leaf 10))
      )

(test (negate (interior-node (interior-node (negative-leaf 0) (negative-leaf 3)) (interior-node (positive-leaf 45) (negative-leaf 50000000))))
      (interior-node (interior-node (positive-leaf 0) (positive-leaf 3)) (interior-node (negative-leaf 45) (positive-leaf 50000000)))
      )

;;add tests:
(test (add (positive-leaf 5) 3)
      (positive-leaf 8)
      )
(test (add (positive-leaf 5) -7)
      (negative-leaf 2)
      )
(test (add (positive-leaf 5) -5)
      (negative-leaf 0)
      )
(test (add (interior-node (interior-node (positive-leaf 5) (negative-leaf 4))
                          (positive-leaf 3))
           -4)
      (interior-node (interior-node (positive-leaf 1) (negative-leaf 8))
                     (negative-leaf 1)))
(test (add (interior-node (negative-leaf 1) (interior-node (positive-leaf 9) (negative-leaf 0))) 0)
      (interior-node (negative-leaf 1) (interior-node (positive-leaf 9) (negative-leaf 0))))

;;positive-thinking tests:
(test (positive-thinking (positive-leaf 4))
      (positive-leaf 4))
(test (positive-thinking (negative-leaf 3))
      #f)
(test (positive-thinking (interior-node(positive-leaf 3) (positive-leaf 6)))
      (interior-node(positive-leaf 3) (positive-leaf 6)))
(test (positive-thinking (interior-node(positive-leaf 3) (negative-leaf 6)))
      (positive-leaf 3))
(test (positive-thinking (interior-node(negative-leaf 1) (negative-leaf 7)))
      #f)
(test (positive-thinking (interior-node (interior-node (positive-leaf 5) (negative-leaf 4)) (interior-node (negative-leaf 2) (positive-leaf 10)))
                         )
      (interior-node(positive-leaf 5) (positive-leaf 10)))

(test (positive-thinking (interior-node (interior-node (positive-leaf 5) (positive-leaf 4)) (interior-node (negative-leaf 2) (positive-leaf 10))))
      (interior-node (interior-node (positive-leaf 5) (positive-leaf 4)) (positive-leaf 10)))



