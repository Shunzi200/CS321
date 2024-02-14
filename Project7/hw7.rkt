#lang plaitypus

;; you may use these definitions in your solution
(print-only-errors #t)

(define-type TLFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TLFAE) (r : TLFAE)]
  [sub (l : TLFAE) (r : TLFAE)]
  [eql (l : TLFAE) (r : TLFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TLFAE) (thn : TLFAE) (els : TLFAE)]
  [fun (arg : symbol) (typ : Type) (body : TLFAE)]
  [app (rator : TLFAE) (rand : TLFAE)]
  [consl (fst : TLFAE) (rst : TLFAE)]
  [firstl (lst : TLFAE)]
  [restl (lst : TLFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TLFAE)]
  [makevector (size : TLFAE) (initial : TLFAE)]
  [set (vec : TLFAE) (index : TLFAE) (val : TLFAE)]
  [lengthl (col : TLFAE)]
  [get (col : TLFAE) (index : TLFAE)])

(define-type Type
  [numberT]
  [booleanT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)]
  [vectorT (typ : Type)])


(define-type envType
  [mtEnv]
  [envBind (name : symbol)
           (type : Type)
           (rest : envType)])


(define parse : (s-expression -> TLFAE)
  (lambda (s-exp)
    (cond
      [(s-exp-number? s-exp)
       (num (s-exp->number s-exp))]
      [(s-exp-symbol? s-exp)
       (case (s-exp->symbol s-exp)
         [(true)  (bool #t)]
         [(false) (bool #f)]
         [else (id (s-exp->symbol s-exp))])]
      [(s-exp-list? s-exp)
       (define as-list (s-exp->list s-exp))
       (cond [(empty? as-list)
              (error 'parse "the empty list is not a valid TLFAE")]
             [(s-exp-symbol? (first as-list))
              (case (s-exp->symbol (first as-list))
                [(+)
                 (check-pieces as-list "add" 3)
                 (add (parse (second as-list))
                      (parse (third as-list)))]
                [(-)
                 (check-pieces as-list "sub" 3)
                 (sub (parse (second as-list))
                      (parse (third as-list)))]
                [(=)
                 (check-pieces as-list "eql" 3)
                 (eql (parse (second as-list))
                      (parse (third as-list)))]
                [(if)
                 (check-pieces as-list "if" 4)
                 (ifthenelse (parse (second as-list))
                             (parse (third as-list))
                             (parse (fourth as-list)))]
                [(fun)
                 (check-pieces as-list "fun" 3)
                 (unless (s-exp-list? (second as-list))
                   (error 'parse "expected parameter list"))
                 (define param-list (s-exp->list (second as-list)))
                 (check-pieces param-list "parameter list" 3)
                 (unless (s-exp-symbol? (first param-list))
                   (error 'parse "expected symbol as parameter name"))
                 (unless (and (s-exp-symbol? (second param-list))
                              (equal? ': (s-exp->symbol (second param-list))))
                   (error 'parse "expected `:`"))
                 (fun (s-exp->symbol (first param-list))
                      (parse-type (third param-list))
                      (parse (third as-list)))]
                [(cons)
                 (check-pieces as-list "cons" 3)
                 (consl (parse (second as-list))
                        (parse (third as-list)))]
                [(first)
                 (check-pieces as-list "first" 2)
                 (firstl (parse (second as-list)))]
                [(rest)
                 (check-pieces as-list "rest" 2)
                 (restl (parse (second as-list)))]
                [(nil)
                 (check-pieces as-list "nil" 2)
                 (nil (parse-type (second as-list)))]
                [(empty?)
                 (check-pieces as-list "empty?" 2)
                 (mtl? (parse (second as-list)))]
                [(make-vector)
                 (check-pieces as-list "make-vector" 3)
                 (makevector (parse (second as-list))
                             (parse (third as-list)))]
                [(set)
                 (check-pieces as-list "set" 4)
                 (set (parse (second as-list))
                      (parse (third as-list))
                      (parse (fourth as-list)))]
                [(length)
                 (check-pieces as-list "length" 2)
                 (lengthl (parse (second as-list)))]
                [(get)
                 (check-pieces as-list "get" 3)
                 (get (parse (second as-list))
                      (parse (third as-list)))]
                [else (parse-app as-list)])]
             [else (parse-app as-list)])]
      [else
       (error 'parse "expected TLFAE")])))

(define parse-app : ((listof s-expression) -> TLFAE)
  (lambda (s-exps)
    (check-pieces s-exps "app" 2)
    (app (parse (first  s-exps))
         (parse (second s-exps)))))

(define parse-type : (s-expression -> Type)
  (lambda (s-exp)
    (cond [(and (s-exp-symbol? s-exp)
                (equal? 'number (s-exp->symbol s-exp)))
           (numberT)]
          [(and (s-exp-symbol? s-exp)
                (equal? 'boolean (s-exp->symbol s-exp)))
           (booleanT)]
          [(s-exp-list? s-exp)
           (define as-list (s-exp->list s-exp))
           (case (length as-list)
             [(2)
              (unless (s-exp-symbol? (first as-list))
                (error 'parse "expected `listof` or `vectorof`"))
              (case (s-exp->symbol (first as-list))
                [(listof)
                 (listT (parse-type (second as-list)))]
                [(vectorof)
                 (vectorT (parse-type (second as-list)))]
                [else
                 (error 'parse "expected `listof` or `vectorof`")])]
             [(3)
              (unless (and (s-exp-symbol? (second as-list))
                           (equal? '-> (s-exp->symbol (second as-list))))
                (error 'parse "expected `->`"))
              (arrowT (parse-type (first as-list))
                      (parse-type (third as-list)))]
             [else (error 'parse-type "expected type")])]
          [else (error 'parse-type "expected type")])))

(define check-pieces : ((listof s-expression) string number -> void)
  (lambda (s-exps expected n-pieces)
    (unless (= n-pieces (length s-exps))
      (error 'parse
             (string-append (string-append "expected " expected)
                            (string-append " got " (to-string s-exps)))))))

(define lookup-symbol : (symbol envType -> Type)
  (lambda (symbolName env)
    (type-case envType env
      [mtEnv () (error 'typecheck
                       "free identifier")]
      [envBind (symbolName2 type rest)
               (if (equal? symbolName symbolName2)
                   type
                   (lookup-symbol symbolName rest))])))

(define type-check : (TLFAE envType -> Type)
  (lambda (a-tlfae env)
    (type-case TLFAE a-tlfae
      [num (n) (numberT)]  
      [bool (b) (booleanT)]  
      [add (l r) 
           (let ([l-type (type-check l env)]
                 [r-type (type-check r env)])
             (if (and (equal? l-type (numberT))
                      (equal? r-type (numberT)))
                 (numberT) 
                 (error 'type-check "add: expected number for both operands")))
           ]
      [sub (l r) 
           (let ([l-type (type-check l env)]
                 [r-type (type-check r env)])
             (if (and (equal? l-type (numberT))
                      (equal? r-type (numberT)))
                 (numberT) 
                 (error 'type-check "sub: expected number for both operands")))
           ]

      [eql (l r)
           (let ([l-type (type-check l env)]
                 [r-type (type-check r env)])
             (if (and (equal? l-type (numberT))
                      (equal? r-type (numberT)))
                 (booleanT) 
                 (error 'type-check "eq: expected number for both operands")))
           ]

      [id (symbolName) (lookup-symbol symbolName env)]
      [ifthenelse (condition th el)
                  (let ([condition-type (type-check condition env)]
                        [th-type (type-check th env)]
                        [el-type (type-check el env)]
                        )
                    (if (equal? condition-type (booleanT))
                        (if   
                         (equal? th-type el-type)
                      
                         th-type
                         (error 'type-check "ifthenelse: type mismatch"))
                        (error 'type-check "ifthenelse: expected boolean"))
                    )
                      
                  ]
      [fun (symbolName args body)
           (arrowT args
                   (type-check body (envBind symbolName
                                             args
                                             env)))]

      [app (function argument)
           (type-case Type (type-check function env)
             [arrowT (argument-type r-type)
                     (if (equal? argument-type
                                 (type-check argument env))
                         r-type
                         (error
                          'type-check
                          "app: type mismatch"))]
             [else (error 'type-check
                          "app: expected function")])]
      [consl
       (firstE restE)
       (let ([firstE-type (type-check firstE env)]
             [restE-type (type-check restE env)])
         (type-case Type restE-type
           [listT (restE-type)
                  (if (equal? firstE-type restE-type)
                      (listT restE-type)
                      (error 'type-check "cons: type mismatch")
                      )]
           [else (error 'type-check "cons: expected list")]
           ))]
     
      [firstl (firstE)
              (let ([firstE-type (type-check firstE env)])
                (type-case Type firstE-type
                  [listT (firstE-type) firstE-type]
                  [else (error 'type-check "first: expected list")]))]
      [restl (restE)
             (let ([restE-type (type-check restE env)])
               (type-case Type restE-type
                 [listT (restE-type) (listT restE-type)]
                 [else (error 'type-check "rest: expected list")]))]
      [nil (list-type) (listT list-type)]
      
      [mtl? (eList)
            (let ([eList-type (type-check eList env)])
              (type-case Type eList-type
                [listT (eList-type)
                       eList-type]
                [else (error 'type-check "empty?: expected list")]))

                ]
      
      [else (error 'type-check "Unknown TLFAE type")]
      )))


(define typecheck-expr : (TLFAE -> Type)
  (lambda (a-tlfae)
    (type-check a-tlfae (mtEnv))))

(test/exn (typecheck-expr (parse `{+ {+ 9 true} 6}))
          "expected number")
(test (typecheck-expr (parse `{+ 5 6}))
      (numberT))

(test (typecheck-expr (parse `{+ {+ 12 7} 15}))
      (numberT))

(test (typecheck-expr (parse `{- 1 6}))
      (numberT))

(test/exn (typecheck-expr (parse `{+ {- 5 true} 6}))
          "expected number")


(test (typecheck-expr (parse `{= 5 8}))
      (booleanT))


(test (typecheck-expr (parse `{= {- 0 4} 2}))
      (booleanT))

(test (typecheck-expr (num 2))
      (numberT))
(test (typecheck-expr (bool #t))
      (booleanT))

(test/exn (typecheck-expr (parse `{= {- 5 true} 6}))
          "expected number")


(test (typecheck-expr (parse `{if {= 8 5} 5 6}))
      (numberT))


(test (typecheck-expr (parse `{if true 5 9}))
      (numberT))


(test/exn (typecheck-expr (parse `{if {= 1 7} true 6}))
          "type mismatch")

(test/exn (typecheck-expr (parse `{if {+ 5 0} true 6}))
          "expected boolean")

(test (lookup-symbol 'x (envBind 'x (arrowT (numberT) (numberT)) (mtEnv)))
      (arrowT (numberT) (numberT)))

(test/exn (lookup-symbol 'y (envBind 'x (arrowT (numberT) (numberT)) (mtEnv)))
          "free identifier")

(test (typecheck-expr
       (parse `{fun {y : number} {+ y 5}}))
      (arrowT (numberT) (numberT)))

(test (typecheck-expr
       (parse `{{fun {y : number} {+ y 9}} 6}))
      (numberT))

(test/exn (typecheck-expr
           (parse `{{fun {y : number} {+ y 5}} true}))
          "type mismatch")

(test (typecheck-expr (parse '{cons 2 {cons 1 {nil number}}}))
      (listT (numberT)))

(test (typecheck-expr (parse '{cons false {cons true {nil boolean}}}))
      (listT (booleanT)))

(test/exn (typecheck-expr (parse '{cons 3 {cons true {nil number}}}))
          "type mismatch")

(test (typecheck-expr (parse `{rest {cons 2 {nil number}}}))
      (listT (numberT)))


(test (typecheck-expr (parse `{rest {cons false {cons true {nil boolean}}}}))
      (listT (booleanT)))

(test (typecheck-expr (parse `{first {cons false {cons true {nil boolean}}}}))
      (booleanT))


(test (typecheck-expr (parse `{empty? {cons false {cons true {nil boolean}}}}))
      (booleanT))


(test (typecheck-expr (parse `{empty? {cons 4 {cons 5 {nil number}}}}))
      (numberT))

