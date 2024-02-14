#lang plai

(print-only-errors)

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
       (arg-expr (listof fnWAE?))])

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body fnWAE?)])

#|
<FunDef> ::= {deffun {<id> <id>*} <fnWAE>}
<fnWAE> ::= <num>
         | {+ <fnWAE> <fnWAE>}
         | {- <fnWAE> <fnWAE>}
         | {with {<id> <fnWAE>} <fnWAE>}
         | <id>
         | {<id> <fnWAE>*}
|#

;; parse : s-expression -> fnWAE?
(define (parse s-exp)
  (cond [(number? s-exp) (num s-exp)]
        [(symbol? s-exp) (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid fnWAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp 3 "addition")
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp 3 "subtraction")
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp 3 "with")
            (check-pieces (second s-exp) 2 "with binding pair")
            (unless (symbol? (first (second s-exp)))
              (error 'parse "expected variable name, got: ~a" (first (second s-exp))))
            (with (first (second s-exp))
                  (parse (second (second s-exp)))
                  (parse (third s-exp)))]
           [else
            ;;(check-pieces s-exp 2 "function application")
            (unless (symbol? (first s-exp))
              (error 'parse "expected a function name, got: ~a" (first s-exp)))
            (app (first s-exp)
                 (map parse (rest s-exp)))])]
        [else
         (error 'parse "expected an fnWAE, got: ~a" s-exp)]))

(define (parse-defn s-exp)
  (check-pieces s-exp 3 "deffun")
  (countParams (second s-exp))
  (fundef (first (second s-exp))
          (rest (second s-exp))
          (parse (third s-exp))))

(define (check-pieces s-exp n-pieces expected)
  (unless (and (list? s-exp)
               (= (length s-exp) n-pieces))
    (error 'parse "expected ~a, got: ~a" expected s-exp)))

(define (countParams  params)
  (unless (null? params)
      (if (equal? #f (member (first params)  (rest params)))
      (countParams (rest params))
       (error 'parse-defn "bad syntax: ~a" params))))

(test (parse `1)
      (num 1))
(test (parse `x)
      (id 'x))
(test (parse `{+ 1 2})
      (add (num 1) (num 2)))
(test (parse `{- 1 2})
      (sub (num 1) (num 2)))
(test (parse `{+ 1 {+ 2 3}})
      (add (num 1) (add (num 2) (num 3))))
(test (parse `{with {x 3} {+ x 2}})
      (with 'x (num 3) (add (id 'x) (num 2))))
(test/exn (parse `{1 2})
          "expected a function name")
(test/exn (parse `{+ 1 2 3})
          "expected addition")


;; ----------------------------------------------------------------------

;; interp : fnWAE? (listof FunDef?) -> number?
(define (interp an-fnwae fundefs)
  (type-case fnWAE an-fnwae
    [num (n) n]
    [add (lhs rhs)
         (+ (interp lhs fundefs)
            (interp rhs fundefs))]
    [sub (lhs rhs)
         (- (interp lhs fundefs)
            (interp rhs fundefs))]
    [with (name named-expr body)
          (interp (subst body
                         name
                         (interp named-expr fundefs))
                  fundefs)]
    [id (name)
        (error 'interp "free identifier: ~a" name)]
    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))
         (define params (fundef-param-name the-fundef))
         (define args (map (lambda (arg) (interp arg fundefs)) arg-expr))
         (define body (fundef-body the-fundef))
         (unless (equal? (length params) (length args))
           (error 'parse "wrong arity: num params ~a num args ~a" (- (length params) 0) (length args)))
         (interp (helper-subst body params args) fundefs)
         
         ]
    ))

(define (lookup-fundef name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" name)]
        [(equal? name (fundef-fun-name (first fundefs)))
         (first fundefs)]
        [else
         (lookup-fundef name (rest fundefs))]))

;; subst : fnWAE? symbol? number? -> fnWAE?
(define (subst a-fnwae name value)
  (type-case fnWAE a-fnwae
    [num (n)
         a-fnwae]
    [add (l r)
         (add (subst l name value)
              (subst r name value))]
    [sub (l r)
         (sub (subst l name value)
              (subst r name value))]
    [with (name2 named-expr body)
          (with name2 (subst named-expr name value)
                (if (equal? name name2)
                    body
                    (subst body name value)))]
    [id (name2)
        (if (equal? name name2)
            (num value)
            a-fnwae)]
    [app (fun-name arg-expr)
         (app fun-name (map (lambda (arg) (subst arg name value)) arg-expr))]))

;; helper-subst fnWae? (list fnWAE?)  (list fnWAE?) -> fnWAE?
(define (helper-subst body params args)
  (if (null? params)
      body
      (helper-subst (subst body (first params) (first args))
                    (rest params)
                    (rest args))))
;;failed test
(test (interp
  (parse '(f 1 2))
  (list
   (parse-defn '(deffun (f x y) (g y x)))
   (parse-defn '(deffun (g x y) x))))
      2)
(test (interp
  (parse '(f 1 2))
  (list
   (parse-defn '(deffun (f x y) (g y x)))
   (parse-defn '(deffun (g x y) y))))
      1)
(test (interp
  (parse '(f (f 1 2) (f 3 2)))
  (list
   (parse-defn '(deffun (f x y) (g y x)))
   (parse-defn '(deffun (g x y) (+ y x)))))
      8)



;;parser and interp tests
(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5})))
      10)

(test (interp (parse '{+ {f 1} {f 10}})
              (list (parse-defn '{deffun {f x} {+ 5 x}})))
      21)


(test (interp (parse '{f 1 2 3})
              (list (parse-defn '{deffun {f x y z} {+ x {- z y}}})))
      2)

(test (interp (parse '{+ 3 {f}})
              (list (parse-defn '{deffun {f} 0})))
      3)

(test (interp (parse '{- {f1 3 4} {f2 5 6}})
              (list (parse-defn '{deffun {f1 x y} {+ x y}})
                    (parse-defn '{deffun {f2 z w} {- w z}})))
      6)

(test (interp (parse '{+ 3 {f 3 5 7}})
              (list (parse-defn '{deffun {f x y z} x})))
      6)

;;error test
(test/exn (interp (parse '{with {x y} 1})
                  (list))
          "free identifier")
(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}})))
          "bad syntax")
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")
(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")
(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x} {+ x x}})))
          "wrong arity")

(test/exn (interp (parse '{f 1 2 3 4 5 6 7 8 9 10})
                  (list (parse-defn '{deffun {f x y a q r t i o y} {+ x x}})))
          "bad syntax")

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f y f h} {+ x x}})))
          "bad syntax")

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f y} {+ x x}})))
          "wrong arity")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {x f} 3})))
          "undefined function")
(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f y} x})))
          "free identifier")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f y} x})))
          "free identifier")

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f a} 5})
                        (parse-defn '{deffun {f a b} {+ a b}})))
          "wrong arity")




