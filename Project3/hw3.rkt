#lang plai

(print-only-errors)

#|
<FNWAE> ::= <num>
| {+ <FNWAE> <FNWAE>}
| {- <FNWAE> <FNWAE>}
| {with {<id> <FNWAE>} <FNWAE>}
| <id>
| {if0 <FNWAE> <FNWAE> <FNWAE>}
| {fun {<id>*} <FNWAE>}
| {<FNWAE> <FNWAE>*} ;; application expressions


<FAE> ::= <num>
| {+ <FAE> <FAE>}
| {- <FAE> <FAE>}
| <id>
| {if0 <FAE> <FAE> <FAE>}
| {fun {<id>} <FAE>}
| {<FAE> <FAE>} ;; application expressions

|#


(define-type FNWAE
  [W-num (n number?)]
  [W-add (lhs FNWAE?)
         (rhs FNWAE?)]
  [W-sub (lhs FNWAE?)
         (rhs FNWAE?)]
  [W-with (name symbol?)
          (named-expr FNWAE?)
          (body FNWAE?)]
  [W-id (name symbol?)]
  [W-if0 (tst FNWAE?)
         (thn FNWAE?)
         (els FNWAE?)]
  [W-fun (params (listof symbol?))
         (body FNWAE?)]
  [W-app (fun-expr FNWAE?)
         (arg-exprs (listof FNWAE?))])

(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [id (name symbol?)]
  [if0 (test FAE?) (then FAE?) (else FAE?)]
  [fun (param symbol?) (body FAE?)]
  [app (fun FAE?) (arg FAE?)])


(define-type FAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body FAE?)
            (ds DefSub?)])

(define-type DefSub
  [mtSub]
  [aSub (name  symbol?)
        (value FAE-Value?)
        (rest  DefSub?)])


;; Helpers ----------------------------------------------------------------------
(define (check-pieces s-expr n-pieces who)
  (unless (= n-pieces (length s-expr))
    (error 'parse "expected ~a, got ~a" who s-expr)))

(define (numop op l r ds)
  (define l-val (interp l ds))
  (define r-val (interp r ds))
  (unless (and (numV? l-val) (numV? r-val))
    (error 'interp "expected number"))
  (numV (op (numV-n l-val) (numV-n r-val))))

(define (helper-fun params body)
  (if (null? params)
      (compile body)
      (fun (car params) (helper-fun (cdr params) body))))

(define (helper-app f args)
  (foldl (lambda (arg acc) (app acc (compile arg))) (compile f) args))





(define initial-def-sub (mtSub))

;; lookup : symbol? DefSub? -> FAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; FAE? -> FAE?
(define (try-constant-fold an-fae)
  ;; Local function definition: we can refer to `an-fae`
  (define (try-fold-op op l r)
    (if (and (num? l)
             (num? r))
        (num (op (num-n l) (num-n r)))
        an-fae))
  (type-case FAE an-fae
    [add (l r)
         (try-fold-op + l r)]
    [sub (l r)
         (try-fold-op - l r)]
    [else an-fae]))

;; parse : s-expression -> fnWAE? ----------------------------------------------------------------------
(define (parse s-expr)
  (cond [(number? s-expr)
         (W-num s-expr)]
        [(symbol? s-expr)
         (W-id s-expr)]
        [(list? s-expr)
         (when (empty? s-expr)
           (error 'parse "the empty list is not a valid fnWAE"))
         (case (first s-expr)
           [(+)
            (check-pieces s-expr 3 "add")
            (W-add (parse (second s-expr))
                   (parse (third s-expr)))]
           [(-)
            (check-pieces s-expr 3 "sub")
            (W-sub (parse (second s-expr))
                   (parse (third s-expr)))]
           [(with)
            (check-pieces s-expr 3 "with")
            (check-pieces (second s-expr) 2 "with binding pair")
            (unless (symbol? (first (second s-expr)))
              (error 'parse "expected variable name, got ~a" (first (second s-expr))))
            (W-with (first (second s-expr))
                    (parse (second (second s-expr)))
                    (parse (third s-expr)))]
           [(if0)
            (check-pieces s-expr 4 "if0")
            (W-if0 (parse (first (rest s-expr)))
                   (parse (second (rest s-expr)))
                   (parse (third (rest s-expr)))
                   )]
           [(fun)
            (W-fun (map (lambda (param)
                          (unless (symbol? param)
                            (error 'parse "expected parameter, got ~a" param))
                          param)
                        (second s-expr))
                   (parse (third s-expr)))]
           [else
            (W-app (parse (first s-expr))
                   (map parse (rest s-expr)))])]
        [else
         (error 'parse "expected FNWAE, got ~a" s-expr)]))

;;parse tests
(test (parse `{+ 1 2})
      (W-add (W-num 1) (W-num 2)))
    

(test (parse `{with {x 3} {+ x 2}})
      (W-with 'x (W-num 3) (W-add (W-id 'x) (W-num 2)))
      )

(test (parse `{+ 2 {with {x 3} {+ x 2}}})
      (W-add
       (W-num 2)
       (W-with 'x (W-num 3) (W-add (W-id 'x) (W-num 2)))))

(test (parse `{with {x 3} {with {y 2} {+ x y}}})
      (W-with'x
             (W-num 3)
             (W-with 'y (W-num 2) (W-add (W-id 'x) (W-id 'y)))))
    
(test (parse `{+ 1 {+ 2 3}})
      (W-add (W-num 1) (W-add (W-num 2) (W-num 3))))


(test (parse `{+ 2 {+ 3 x}})
      (W-add (W-num 2) (W-add (W-num 3) (W-id 'x))))

(test (parse `{+ x {+ 2 3}})
      (W-add (W-id 'x) (W-add (W-num 2) (W-num 3))))


;; compile : FNWAE? -> FAE? ----------------------------------------------------------------------
(define (compile an-fwae)
  ;; {with {x <FWAE 1>} <FWAE 2>}
  ;; {{fun x <FWAE 2>} <FWAE 1>}
  (type-case FNWAE an-fwae
    [W-num (n) (num n)]
    [W-id (name) (id name)]
    [W-add (l r)
           (try-constant-fold
            (add (compile l)
                 (compile r)))]
    [W-sub (l r)
           (try-constant-fold
            (sub (compile l)
                 (compile r)))]
    [W-if0 (condition res1 res2)
           (if0 (compile condition) (compile res1) (compile res2))]
    [W-fun (params body)
           (if (null? params)
               (error "nullary function")
               (helper-fun params body)
               )
           ]
    [W-app (f args)
           (if (null? args)
               (error "nullary application")
               (helper-app f args))
           ]
    
    [W-with (name named-expr body)
            (app (fun name (compile body))
                 (compile named-expr))]))


;;compile tests
(test (compile (parse `{+ 1 2}))
      (num 3))
    

(test (compile (parse `{with {x 3} {+ x 2}}))
      (app (fun 'x (add (id 'x) (num 2))) (num 3)))
  

(test (compile (parse `{+ 2 {with {x 3} {+ x 2}}}))
      (add (num 2) (app (fun 'x (add (id 'x) (num 2))) (num 3)))
      )

(test (compile (parse `{with {x 3} {with {y 2} {+ x y}}}))
      (app
       (fun 'x (app (fun 'y (add (id 'x) (id 'y))) (num 2)))
       (num 3))
      )
    
(test (compile (parse `{+ 1 {+ 2 3}}))
      (num 6))


(test (compile (parse `{+ 2 {+ 3 x}}))
      (add (num 2) (add (num 3) (id 'x))))

(test (compile (parse `{+ x {+ 2 3}}))
      (add (id 'x) (num 5)))

(test (compile (parse `{if0 0 1 2}))
      (if0 (num 0) (num 1) (num 2)))

(test (compile (parse `{if0 {+ 0 2} 1 2}))
      (if0 (num 2) (num 1) (num 2)))



;; interp : FAE? DefSub? -> FAE-Value?  ----------------------------------------------------------------------
(define (interp an-fae ds)
  (type-case FAE an-fae
    [num (n) (numV n)]
    [add (l r) (numop + l r ds)]
    [sub (l r) (numop - l r ds)]
    [id (name) (lookup name ds)]
    [if0 (condition res1 res2)
         (if (equal? (numV 0) (interp condition ds))
             (interp res1 ds)
             (interp res2 ds)
             )]

    [fun (param-name body) (closureV param-name body ds)]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))
         (define arg-val (interp arg-expr ds))
         (type-case FAE-Value fun-val
           [closureV (param-name body closed-ds)
                     (interp body
                             (aSub param-name
                                   arg-val
                                   closed-ds))]
           [else (error 'interp "expected function, got ~a" fun-val)])]
    ))


;; interp-expr : FAE? -> number or 'function
(define (interp-expr an-fae)
  (let ([result (interp an-fae (mtSub))])
    (type-case FAE-Value result
      [numV (n) n]
      [closureV (param-name body closed-ds) 'function])))






;;factorial ----------------------------------------------------------------------

(define factorial
  `{with {helperMult {fun {val n acc self}
                          {if0 n
                               acc
                               {self val {- n 1} {+ acc val} self}}
                          }}

         {with {helperRecursion {fun {n acc self}
                                     {if0 n
                                          acc
                                          {self {- n 1} {helperMult acc n 0 helperMult} self}

                                          }}}

               {fun {n}
                    {helperRecursion n 1 helperRecursion}

                    }}}
  )
;;prime? ----------------------------------------------------------------------
(define prime?
  `{with {helper-neg {fun {positive negative self}
                          {if0 positive
                               0
                               {if0 negative
                                    1
                                    {self {+ 1 positive} {- negative 1} self
             
                                          }      
                                    }
                               }
                          }}
         {with {neg? {fun {x}
                          {if0 x
                               1
                               {helper-neg {+ 1 x} {- x 1} helper-neg}
         
                               }     
                          }
                     }

               {with {divisible? {fun {numerator divisor self}
                       {if0 numerator
                            1 
                            {if0 {neg? {-  numerator divisor}}
                                 0
                                 {self {- numerator divisor} divisor self} 
                                 
                                 }}}}
                     {with {helperPrime {fun {main x self}
                                  {if0 {- main x}
                                       1
                                       {if0 {divisible? main x divisible?}
                                            {self main {+ x 1} self}
                                            0
                                            }}}}
                           


                {fun {n}
                     {if0 {helperPrime n 2 helperPrime}
                          1
                          0}
                     
                     }                               
               }}}}              
)

;;(interp-expr (compile (parse prime?)))

;;(define prime?-test

;;)




;;test cases  ----------------------------------------------------------------------
;;(parse `{with {x 10} {{fun {a y z} {+ z {+ x y}}} 1 2 3}})

(test (interp-expr (compile (parse `{{fun {x} x} 1 })))
      1)
(test (interp-expr (compile (parse `{{fun {x y z} {+ x {+ x y}}} 1 2 3})))
      4)
(test (interp-expr (compile (parse `{with {x 10} {{fun {a y z} {+ a {+ a a}}} 1 2 3}})))
      3
      )

(test (interp-expr (compile (parse `{with {x 10} {{fun {a y z} {+ 0 {+ x z}}} 1 2 3}})))
      13
      )

(test (interp-expr (compile (parse `{with {x 1} {with {x 2} {with {x 3} x}}})))
      3)

(test (interp-expr (compile (parse `{with {x 1}
                                          {with {x 2}
                                                {with {x 3}
                                                      {{fun {x} x} 15}}}})))
      15)

(test (interp-expr (compile (parse `{with {x {{fun {x y} {+ x y}}5 9}} {+ x x}})))
      28)

(test (interp-expr (compile (parse `{{fun {x y} {{fun {x y} {+ x y}} 3 4}} 8 7})))
      7)


(test (interp-expr (compile (parse `{if0 0 1 2})))
      1)

(test (interp-expr (compile (parse `{if0 2 1 2})))
      2)

(test (interp-expr (compile (parse `{{fun {a b c d} {if0 a b c}} {- 45 45} 8 9 7})))
      8 )  
  
;;error
(test/exn (interp (compile (parse `{1 2}))
                  initial-def-sub)
          "expected function")

(test/exn (interp (compile (parse `{+ 1 {fun {x} 10}}))
                  initial-def-sub)
          "expected number")

(test (interp (compile (parse `{with {f {with {x 3}
                                              {fun {y} {+ x y}}}}
                                     {f 5}}))
              initial-def-sub)
      (numV 8))

(test/exn (interp (compile (parse `{with {z {fun {x} {+ x y}}}
                                         {with {y 10} {z y}}}))
                  initial-def-sub)
          "free identifier")


(test/exn (compile (parse `{fun {} 0})) 
          "nullary function")

;;Given test cases
(test/exn (interp-expr (compile (parse `{+ {fun {x} x}
                                           {1 2}})))
          "expected function")
(test (interp-expr (num 10)) 10)
(test (interp-expr (fun 'x (id 'x))) 'function)


;;Failed first try

(test (interp-expr (compile (parse `(,prime? 2))))
0)

(test (interp-expr (compile (parse `(,prime? 3))))
0)

(test (interp-expr (compile (parse `(,prime? 4))))
1)

(test (interp-expr (compile (parse `(,prime? 5))))
0)

(test  (interp-expr (compile (parse `(,prime? 6))))
1)

(test (interp-expr (compile (parse `(,prime? 7))))
0)

(test  (interp-expr (compile (parse `(,prime? 8))))
1)

(test (interp-expr (compile (parse `(,prime? 9))))
1)
(test (interp-expr (compile (parse `(,prime? 10))))
1)

(test (interp-expr (compile (parse `(,prime? 11))))
0)
(test (interp-expr (compile (parse `(,prime? 12))))
1)

(test  (interp-expr (compile (parse `(,prime? 13))))
0)

(test  (interp-expr (compile (parse `(,prime? 14))))
1)
(test  (interp-expr (compile (parse `(,prime? 17))))
0)

(test  (interp-expr (compile (parse `(,prime? 19))))
0)

(test (interp-expr (compile (parse `(,prime? 23))))
0)






