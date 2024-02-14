#lang plai
#|
<EFAE> = <num>
| {+ <EFAE> <EFAE>}
| {- <EFAE> <EFAE>}
| <id>
| {fun {<id>} <EFAE>}
| {<EFAE> <EFAE>} ;; function application
| {if0 <EFAE> <EFAE> <EFAE>}
| {throw <id> <EFAE>}
| {try <EFAE1> {catch {tag <id1> as <id2>} <EFAE2>}}
|#

(print-only-errors)

(define-type EFAE
  [num (n number?)]
  [add (lhs EFAE?)
       (rhs EFAE?)]
  [sub (lhs EFAE?)
       (rhs EFAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body EFAE?)]
  [app (fun-expr EFAE?)
       (arg-expr EFAE?)]
  [if0 (tst EFAE?)
       (thn EFAE?)
       (els EFAE?)]
  [throw (tag symbol?)
         (throw-expr EFAE?)]
  [try-catch (try-body EFAE?)
             (tag symbol?)
             (exn-name symbol?)
             (catch-body EFAE?)])

(define-type EFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body EFAE?)
            (ds DefSub?)]
  [throwV (tag symbol?) (value EFAE-Value?)])

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value EFAE-Value?)
         (rest DefSub?)]
  [cSub (tag symbol?)
        (exn-name symbol?)
        (catch-body EFAE?)
        (rest DefSub?)])



;; ----------------------------------------------------------------------
;; interp-test : s-expression -> EFAE-Value?
(define (interp-test s-exp)
  (with-handlers ([EFAE-Value?
                   (lambda (ret-val)
                     (error 'interp
                            "not inside a function body"))])
    (interp (parse s-exp) (mtSub))))


;; interp : EFAE? DefSub? -> EFAE-Value?
(define (interp a-EFAE ds)
  (type-case EFAE a-EFAE
    [num (n) (numV n)]
    [add (l r)
         (let ([l-val (interp l ds)])
           (cond [(throwV? l-val) l-val]
                 [else
                  (let ([r-val (interp r ds)])
                    (cond [(throwV? r-val) r-val]
                          [else (numop + l-val r-val)]))]))]

    [sub (l r)
         (let ([l-val (interp l ds)])
           (cond [(throwV? l-val) l-val]
                 [else
                  (let ([r-val (interp r ds)])
                    (cond [(throwV? r-val) r-val]
                          [else (numop - l-val r-val)]))]))]

    [id (name)
        (lookup name ds)]
    [fun (param-name body)
         (closureV param-name body ds)]
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))
         (define arg-val (interp arg-expr ds))
         (unless (closureV? fun-val)
           (error 'interp "expected function"))
         (with-handlers ([EFAE-Value? (lambda (ret-val) ret-val)])
           (interp (closureV-body fun-val)
                   (aSub (closureV-param-name fun-val)
                         arg-val
                         (closureV-ds fun-val))))]
    [if0 (condition res1 res2)
         (let ([cond-val (interp condition ds)])
           (cond [(throwV? cond-val) cond-val]
                 [(equal? (numV 0) cond-val) (interp res1 ds)]
                 [else (interp res2 ds)]))]

    [throw (tag throw-expr)
           (let ([res (interp throw-expr ds)])
             (cond
               [(throwV? res) res] 
               [else (throwV tag res)]))] 

    [try-catch (try-body tag exn-name catch-body)
               (let ([res (interp try-body ds)])
                 (type-case EFAE-Value res
                   [throwV (thrown-tag value)
                           (if (eq? thrown-tag tag)
                               (interp catch-body (aSub exn-name value ds))
                               res)]  
                   [else res]))]
    ))


(define (handler tag value ds)
  (type-case DefSub ds
    [mtSub ()
           (error 'interp "missing catch")] 
    [aSub (name2 _ rest)
          (handler tag value rest)]
    [cSub (catch-tag exn-name catch-body rest)
          (if (eq? tag catch-tag)
              (interp catch-body (aSub exn-name value rest))
              (handler tag value rest))]))

;; numop : (number? number? -> number?) EFAE? EFAE? DefSub? -> EFAE-Value?
(define (numop op l-val r-val)
  (if (and (numV? l-val) (numV? r-val))
      (numV (op (numV-n l-val)
                (numV-n r-val)))
      (error 'interp "expected number")))




;; lookup : symbol? DefSub? -> EFAE-Value?
;; lookup : symbol? DefSub? -> EFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub ()
           (error "free identifier")]

    [aSub (name2 value rest)
          (if (equal? name name2)
              value
              (lookup name rest))]

    [cSub (tag exn-name catch-body rest)

          (lookup name rest)]))


(define (interp-expr an-fae)
  (let ([result (interp an-fae (mtSub))])
    (type-case EFAE-Value result
      [numV (n) n]
      [closureV (param-name body closed-ds) 'function]

      [throwV (tag symbol?) (error 'interp "missing catch")])))


;; ----------------------------------------------------------------------
;; parse : s-expression -> EFAE?
(define (parse s-exp)
  (cond [(number? s-exp)
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid EFAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp "add" 3)
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp "sub" 3)
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(if0)
            (check-pieces s-exp "if0" 4)
            (if0 (parse (first (rest s-exp)))
                 (parse (second (rest s-exp)))
                 (parse (third (rest s-exp)))
                 )]
           [(fun)
            (check-pieces s-exp "fun" 3)
            (check-pieces (second s-exp) "parameter list" 1)
            (fun (first (second s-exp))
                 (parse (third s-exp)))]
           [(throw)
            (check-pieces s-exp "ret-0" 3)
            (throw  (second s-exp)
                    (parse (third s-exp)))]
           [(try)
            (try-catch (parse (second s-exp))
                       (second (second (third s-exp)))
                       (fourth (second (third s-exp)))
                       (parse (third (third s-exp))))]
           [else
            (check-pieces s-exp "app" 2)
            (app (parse (first s-exp))
                 (parse (second s-exp)))])]
        [else
         (error 'parse "expected EFAE got ~a" s-exp)]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))

;;tests
(test (interp-expr (parse `{+ 2 {try {+ 4 {throw x 5}}
                                     {catch {tag x as e} {+ 3 e}}}}))
      10)
(test (interp-expr (parse `{try {+ 2 {try {+ 3 {throw y 5}}
                                          {catch {tag x as e} {+ 6 e}}}}
                                {catch {tag y as e} {+ 10 e}}}))
      15)
(test (interp-expr (add
                    (num 2)
                    (try-catch (add (num 4) (throw 'x (num 5))) 'x 'e (add (num 3) (id 'e)))))
      10)

(test (interp-expr (try-catch
                    (add
                     (num 2)
                     (try-catch (add (num 3) (throw 'y (num 5))) 'x 'e (add (num 6) (id 'e))))
                    'y
                    'e
                    (add (num 10) (id 'e))) )
      15)

(test (interp-expr (try-catch
                    (throw 'a (add (throw 'a (add (num 3) (num 1))) (num 10)))
                    'a
                    'j
                    (add (id 'j) (num 5))))
      9)
(test (interp-expr (parse `{try {+ 5 5}
                                {catch {tag a as e} {+ 10 e}}}))
      10)

(test (interp-expr (parse `{try {throw a 5}
                                
                                {catch {tag a as e} {+ 20 e}}}))
      25)

(test (interp-expr (parse `{try 
                            {+ 
                             {try {throw x 3}
                                  {catch {tag x as e} e}}
                             {try {throw y 4}
                                  {catch {tag y as e} e}}}
                            {catch {tag z as e} 0}}))
      7)

(test (interp-expr (parse `{try 
                            {+ 
                             {try {throw x 3}
                                  {catch {tag x as e} e}}
                             {try {throw z 8}
                                  {catch {tag y as e} e}}}
                            {catch {tag z as e} 0}}))
      0)

(test (interp-expr (parse `{try {throw a 3}
                                {catch {tag a as e} {+ 3 {+ e 2}}}}))
      8)

(test (interp-expr (parse `{try
                            {try {throw b 10}
                                 {catch {tag b as e} {+ 50 0}}
                                 }
                            {catch {tag a as e} {+ 0 0}}}))
      50)

(test (interp-expr (parse `{try
                            {try {throw a 10}
                                 {catch {tag b as e} {+ 50 0}}
                                 }
                            {catch {tag a as e} {+ 0 0}}}))
      0)

(test (interp-expr (parse `{try
                            {try {+ 1 2}
                                 {catch {tag b as e} {+ 50 0}}
                                 }
                            {catch {tag a as e} {+ 0 0}}}))
      3)

(test/exn (interp-expr (parse `{try {throw a 1} {catch {tag a as b} {throw a 1}}}))
          "missing catch")

(test/exn (interp-expr (parse `{try {throw a 1} {catch {tag a as b} {throw z 4}}}))
          "missing catch")

(test/exn (interp-expr (parse `{+ 2 {try {throw a 1} {catch {tag a as b} {throw a 1}}}}))
          "missing catch")



;;other tests -----------------
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

(test/exn (interp-test `z)
          "free identifier")

;; ----------

(test (interp-test `{{fun {x} {+ x 1}} 3})
      (numV 4))
(test (interp-test `{fun {x} {+ x 1}})
      (closureV 'x (parse `{+ x 1}) (mtSub)))
(test/exn (interp-test `{1 2})
          "expected function")

(test/exn (interp-test `{+ 1 {fun {x} x}})
          "expected number")


;;Failed tests

(test (interp-expr (parse `(if0 0 1 2)))
      1)

(test(interp-expr (parse `(if0 1 1 2)))
     2)

(test (interp-expr (parse `(+ (if0 0 (+ 10 6) 2) 5)))
      21)

(test (interp-expr (parse `(+ ((fun (x) (if0 x 2 3)) 0) 10)))
      12)

(test/exn(interp-expr (add (throw 'a (num 3)) (app (num 1) (num 1))))
         "missing catch")


(test/exn(interp-expr (add (throw 'a (num 3)) (sub (num 1) (num 1))))
         "missing catch")

(test/exn(interp-expr (add (throw 'a (num 3)) (add (num 1) (num 1))))
         "missing catch")



(test(interp-expr (parse `(try (if0 (throw a 1) 1 2) (catch (tag a as x) 4))))
     4)

(test (interp-expr
       (parse `(+ 2 (try (+ 1 (if0 (throw a 1) 1 2)) (catch (tag a as x) 4)))))
      6)

(test (interp-expr
       (parse `(if0 (try (+ 1 (if0 (throw a 1) 1 2)) (catch (tag a as x) 4)) 0 1)))
      1)

(test(interp-expr
      (parse `(if0 (try (+ 1 (if0 (throw a 1) 1 2)) (catch (tag a as x) 0)) 0 1)))
     0)


(test (interp-expr
       (parse
        `(try
          (try
           (if0
            (+
             2
             (try
              ((fun (f) (f 3)) (fun (x) (throw y 1)))
              (catch (tag a as e) (+ 5 e))))
            100
            101)
           (catch (tag z as e) (+ e 2)))
          (catch (tag y as e) (+ 10 e)))))
      11)

(test (interp-expr (parse `{{fun {c}
                           {try {try {+ 10 {if0 c {throw r 5} {throw a 7}}}
                                {catch {tag r as r} {+ c 10}}}
                                {catch {tag a as o} {+ o 0}
                                } }} 3}
                           ))
      7)
