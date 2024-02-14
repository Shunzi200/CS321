#lang plai
(define eight-principles
  (list
   "Know your rights."
   "Acknowledge your sources."
   "Protect your work."
   "Avoid suspicion."
   "Do your own work."
   "Never falsify a record or permit another person to do so."
   "Never fabricate data, citations, or experimental results."
   "Always tell the truth when discussing your work with your instructor."))

(print-only-errors)

;; <FunDef> = {deffun {<id> <id>*} <fnWAE>}
;; <fnWAE> = <num>
;; | {+ <fnWAE> <fnWAE>}
;; | {- <fnWAE> <fnWAE>}
;; | {with {<id> <fnWAE>} <fnWAE>}
;; | <id>
;; | {<id> <fnWAE>*}
;; | {if0 <fnWAE> <fnWAE> <fnWAE>}

(define-type fnWAE
  [num (n number?)]
  [add (lhs fnWAE?)
       (rhs fnWAE?)]
  [sub (lhs fnWAE?)
       (rhs fnWAE?)]
  [with (name symbol?)
        (bound-expr fnWAE?)
        (body-expr fnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)
       (arg-expr (listof fnWAE?))]
  [if0 (condition fnWAE?)
       (res1 fnWAE?)
       (res2 fnWAE?)
       ]
  )

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body fnWAE?)])

(define-type DefSub
  [mtSub]
  [aSub (name symbol?)
        (value number?)
        (rest DefSub?)])

;; ----------------------------------------------------------------------

;; parse : s-expression -> fnWAE?
(define (parse s-expr)
  (cond [(number? s-expr)
         (num s-expr)]
        [(symbol? s-expr)
         (id s-expr)]
        [(list? s-expr)
         (when (empty? s-expr)
           (error 'parse "the empty list is not a valid fnWAE"))
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "add")
            (add (parse (second s-expr))
                 (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "sub")
            (sub (parse (second s-expr))
                 (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (check-pieces (second s-expr) 2 "with binding pair")
            (unless (symbol? (first (second s-expr)))
              (error 'parse "expected variable name, got ~a" (first (second s-expr))))
            (with (first (second s-expr))
                  (parse (second (second s-expr)))
                  (parse (third s-expr)))]
           [(if0)
            (check-pieces s-expr 4 "if0")
            (if0 (parse (first (rest s-expr)))
                 (parse (second (rest s-expr)))
                 (parse (third (rest s-expr)))
                 )

            ]
           [else
            ;;(check-pieces s-exp 2 "function application")
            (unless (symbol? (first s-expr))
              (error 'parse "expected a function name, got: ~a" (first s-expr)))
            (app (first s-expr)
                 (map parse (rest s-expr)))])]
        [else (error 'parse "expected fnWAE, got ~a" s-expr)]))

(define (parse-defn s-exp)
  (check-pieces s-exp 3 "deffun")
  (countParams (second s-exp))
  (fundef (first (second s-exp))
          (rest (second s-exp))
          (parse (third s-exp))))
(define (countParams  params)
  (unless (null? params)
    (if (equal? #f (member (first params)  (rest params)))
        (countParams (rest params))
        (error 'parse-defn "bad syntax: ~a" params))))

(define (check-pieces s-expr n-pieces who)
  (unless (= n-pieces (length s-expr))
    (error 'parse "expected ~a, got ~a" who s-expr)))

(test (parse `1) (num 1))
(test (parse `y) (id 'y))
(test (parse `{+ 1 2}) (add (num 1) (num 2)))
(test (parse `{- 1 2}) (sub (num 1) (num 2)))
(test (parse `{with {x 3} {+ x 2}}) (with 'x (num 3) (add (id 'x) (num 2))))
(test/exn (parse `{+ 1 2 3}) "expected add")

;; ----------------------------------------------------------------------

;; interp : fnWAE? (listof FunDef?) DefSub? -> number?
(define (interp an-fnwae fundefs ds)
  (type-case fnWAE an-fnwae
    [num (n) n]
    [add (l r) (+ (interp l fundefs ds) (interp r fundefs ds))]
    [sub (l r) (- (interp l fundefs ds) (interp r fundefs ds))]
    [id (name) (lookup name ds)]
    [with (name named-expr body)
          (interp body
                  fundefs
                  (aSub name
                        (interp named-expr fundefs ds)
                        ds))]
    [if0 (condition res1 res2)
         (if (equal? 0 (interp condition fundefs ds))
             (interp res1 fundefs ds)
             (interp res2 fundefs ds)
             )]
    
    [app (fun-name arg-exprs)
         (define the-fundef (lookup-fundef fun-name fundefs))
         (define params (fundef-param-name the-fundef))
         (define args (map (lambda (arg) (interp arg fundefs ds)) arg-exprs))
         (unless (equal? (length params) (length args))
           (error 'parse "wrong arity: num params ~a num args ~a" (- (length params) 0) (length args)))
         (define new-ds 
           (foldr (lambda (param arg prev-ds) 
                    (aSub param arg prev-ds))
                  (mtSub) 
                  (fundef-param-name the-fundef) args))
         (interp (fundef-body the-fundef) fundefs new-ds)]
    ))

;; fnWAE (listof FunDef) -> Number
(define (interp-expr fnwaes fundefs)
  (interp fnwaes fundefs (mtSub))
  )

;; lookup : symbol? DefSub? -> number?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; lookup-fundef : symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? (fundef-fun-name (first fundefs)) fun-name)
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))

(define mult-and-neg-deffuns

  (list `{deffun {helper-neg positive negative}
           {if0 positive
                0
                {if0 negative
                     1
                     {helper-neg {+ 1 positive} {- negative 1}
             
                                 }      
                     }
                }
           }
        `{deffun {neg? x}
           {if0 x
                1
                {helper-neg {+ 1 x} {- x 1}}
         
                }     
           }

    

`{deffun {mult-helper res x y }
   {if0 y
        res
        {if0 {neg? y}
             
             {mult-helper {+ res x} x {+ y 1}}
             {mult-helper {+ res x} x {- y 1}}
             }
   }}
    `{deffun {mult x y}
       {if0 {neg? y}
            {- 0 {mult-helper 0 x y}}
            {mult-helper 0 x y}
            }
   }
        ))

;; ----------------------------------------------------------------------
;; tests Part 1

(define initial-def-sub (mtSub))

;; {deffun {f x} {+ y x}}
;; {with {y 2} {f 10}}
(test (interp-expr (parse '{+ 1 2}) '()) 3)
(test (interp-expr (parse '{- 5 3}) '()) 2)

(test (interp-expr (parse '{with {x 3} x}) '()) 3)
(test (interp-expr (parse '{with {x 3} {+ x 2}}) '()) 5)
(test (interp-expr (parse '{with {x 3} {with {y 4} {+ x y}}}) '()) 7)

(define f-expr (parse-defn '{deffun {f x} {+ x 5}}))
(test (interp-expr (parse '{f 3}) (list f-expr)) 8)

(define g-expr (parse-defn '{deffun {g x} {- x 3}}))
(test (interp-expr (parse '{g {f 2}}) (list f-expr g-expr)) 4)

(test (interp-expr (parse '{with {y 4} {f y}}) (list f-expr)) 9)

(define h-expr (parse-defn '{deffun {h x y} {+ x y}}))
(test (interp-expr (parse '{h 3 4}) (list h-expr)) 7)


(test (interp-expr (parse '{f 1 2})
                   (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
(test (interp-expr (parse '{+ {f} {f}})
                   (list (parse-defn '{deffun {f} 5})))
      10)

(test (interp-expr (parse '{+ {f 1} {f 10}})
                   (list (parse-defn '{deffun {f x} {+ 5 x}})))
      21)


(test (interp-expr (parse '{f 1 2 3})
                   (list (parse-defn '{deffun {f x y z} {+ x {- z y}}})))
      2)

(test (interp-expr (parse '{+ 3 {f}})
                   (list (parse-defn '{deffun {f} 0})))
      3)

(test (interp-expr (parse '{- {f1 3 4} {f2 5 6}})
                   (list (parse-defn '{deffun {f1 x y} {+ x y}})
                         (parse-defn '{deffun {f2 z w} {- w z}})))
      6)

(test (interp-expr (parse '{+ 3 {f 3 5 7}})
                   (list (parse-defn '{deffun {f x y z} x})))
      6)
;;Part 2
(test/exn (interp-expr (parse '{with {x y} 1})
                       (list))
          "free identifier")
(test/exn (interp-expr (parse '{f 1 2})
                       (list (parse-defn '{deffun {f x x} {+ x x}})))
          "bad syntax")
(test/exn (interp-expr (parse '{f x})
                       (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")
(test/exn (interp-expr (parse '{f 1})
                       (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test/exn (interp-expr (parse '{f x})
                       (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")
(test/exn (interp-expr (parse '{f 1 2})
                       (list (parse-defn '{deffun {f x} {+ x x}})))
          "wrong arity")

(test/exn (interp-expr (parse '{f 1 2 3 4 5 6 7 8 9 10})
                       (list (parse-defn '{deffun {f x y a q r t i o y} {+ x x}})))
          "bad syntax")

(test/exn (interp-expr (parse '{f 1 2})
                       (list (parse-defn '{deffun {f y f h} {+ x x}})))
          "bad syntax")

(test/exn (interp-expr (parse '{f 1 2})
                       (list (parse-defn '{deffun {f y} {+ x x}})))
          "wrong arity")

(test/exn (interp-expr (parse '{f x})
                       (list (parse-defn '{deffun {x f} 3})))
          "undefined function")
(test/exn (interp-expr (parse '{f 1})
                       (list (parse-defn '{deffun {f y} x})))
          "free identifier")

(test/exn (interp-expr (parse '{f x})
                       (list (parse-defn '{deffun {f y} x})))
          "free identifier")

(test/exn (interp-expr (parse '{f 1 2})
                       (list (parse-defn '{deffun {f a} 5})
                             (parse-defn '{deffun {f a b} {+ a b}})))
          "wrong arity")


;;test Part 3
(test (interp-expr (parse '{if0 0 1 2}) '()) 1)
(test (interp-expr (parse '{if0 1 2 3}) '()) 3)
(test (interp-expr (parse '{if0 {+ 1 0} 2 3}) '()) 3)
(test (interp-expr (parse '{if0 {- 0 0} 6 3}) '()) 6)
(test (interp-expr (parse '{if0 {- 0 0} {+ 10 1} 3}) '()) 11)
(test (interp-expr (parse '{if0 {f 0} {f 10} 3}) (list (parse-defn '{deffun {f y} y}))) 10)


;; test Part 4
(test (interp-expr (parse '{neg? 0}) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse '{neg? -1}) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse '{neg? 1}) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse '{neg? -2}) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse '{neg? 2}) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse '{neg? -1000}) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse '{neg? 1000}) (map parse-defn mult-and-neg-deffuns)) 1)


;;test Part 5
(test (interp-expr (parse '{mult 1 2}) (map parse-defn mult-and-neg-deffuns)) 2)
(test (interp-expr (parse '{mult -1 2}) (map parse-defn mult-and-neg-deffuns)) -2)
(test (interp-expr (parse '{mult 1 -2}) (map parse-defn mult-and-neg-deffuns)) -2)
(test (interp-expr (parse '{mult -3 -2}) (map parse-defn mult-and-neg-deffuns)) 6)
(test (interp-expr (parse '{mult 10 0}) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse '{mult 0 10}) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse '{mult 1000 -10}) (map parse-defn mult-and-neg-deffuns)) -10000)





