;; PL Project - Fall 2021
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

;; CHANGE add the missing ones

(struct var      (string)         #:transparent)  ;; a variable, e.g., (var "foo")
(struct num      (int)            #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool     (boolean)        #:transparent)
(struct plus     (e1 e2)          #:transparent)  ;; add two expressions
(struct minus    (e1 e2)          #:transparent)  ;; minus two expressions
(struct mult     (e1 e2)          #:transparent)  ;; multiply two expressions
(struct div      (e1 e2)          #:transparent)  ;; divide two expressions
(struct neg      (e1)             #:transparent)  ;; negation of an expression
(struct andalso  (e1 e2)          #:transparent)  ;; AND Logical of two expressions
(struct orelse   (e1 e2)          #:transparent)  ;; OR Logical of two expressions
(struct cnd      (e1 e2 e3)       #:transparent)  ;; cond (e1 e2 e3): if e1 then e2 else e3
(struct iseq     (e1 e2)          #:transparent)  ;; True if e1 equal to e2
(struct ifnzero  (e1 e2 e3)       #:transparent)  ;; if (e1 is not 0) then e2 else e3
(struct ifleq    (e1 e2 e3 e4)    #:transparent)  ;; if (e1 >> e2) then e4 else e3



(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct tlam  (nameopt formal arg-type body) #:transparent) ;; a typed argument, recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application
(struct with     (s e1 e2)       #:transparent)  ;; a let expression where the value of e1 is bound to s in e2
(struct apair    (e1 e2)          #:transparent)  ;; pair constructor
(struct 1st      (e1)             #:transparent)  ;; the first part of a pair
(struct 2nd      (e1)             #:transparent)  ;; the second part of a pair


(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e)     #:transparent) ;; if e1 is unit then true else false

;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 


(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k r) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r

(struct letrec (s1 e1 s2 e2 s3 e3 s4 e4 e5) #:transparent) ;; a letrec expression for recursive definitions

;; Type structures
;; Primitive types are: "int", "bool" and "null"
(struct collection (type) #:transparent) ;; collection of a certain type, e.g., (collection "int")
(struct function (input-type output-type) #:transparent) ;; e.g. (function ("int" int")) means fn f "int" -> "int"

;; Problem 1
(define (racketlist->numexlist xs) (
                                    cond
                                     [(null? xs) (munit)]
                                     [else (apair (car xs) (racketlist->numexlist (cdr xs)))]
                                    ))
(define (numexlist->racketlist xs) (
                                    cond
                                     [(munit? xs) null]
                                     [else (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]
                                    ))
;(racketlist->numexlist '(1 2 3))
;(apair 1 2)
;(numexlist->racketlist (racketlist->numexlist '(1 2 3)))
;;------------------------------------------------------------------------------------------------------------------------------------------
;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [else (
               if (equal? (car (car env)) str)
                  (cdr (car env))
                  (envlookup (cdr env) str)
               )]
		)
 )
(define (merge_two_env env1 env2) (
                                   cond
                                    [(> (length env2) 3000 ) (error "error: stack over flow")]
                                    [(null? env1) env2]
                                    [else (merge_two_env (cdr env1) (cons (car env1) env2))]

                                   ))
(define (search_value_in_records s r) (
                                       cond
                                        [(munit? r) r]
                                        [(equal? s (key-s (record-k r)))  (key-e (record-k r)) ]
                                        [else (search_value_in_records s (record-r r))]
                                       ))
;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  
  (cond [(var? e)
         (envlookup env (var-string e))]

        [(plus? e)
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number")))]

        [(minus? e)
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]

        [(mult? e)
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiplication applied to non-number")))]

        [(div? e)
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (quotient (num-int v1) 
                       (num-int v2)))
               (error "NUMEX division applied to non-number")))]

        [(andalso? e)
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           [if (bool? v1)
               (if (bool-boolean v1)
                   (let ([v2 (eval-under-env (andalso-e2 e) env)])
                     (if (bool? v2)
                         (if (equal? (bool-boolean v2) #t) (bool #t) (bool #f))
                         (error "NUMEX andalso applied to non-boolean")))
                   (bool #f)
                   )
               (error "NUMEX andalso applied to non-boolean")])]

        [(orelse? e)
         (let ([v1 (eval-under-env (orelse-e1 e) env)])
           [if (bool? v1)
               (if (bool-boolean v1)
                   (bool #t)
                   (let ([v2 (eval-under-env (orelse-e2 e) env)])
                     (if (bool? v2)
                         (if (equal? (bool-boolean v2) #t) (bool #t) (bool #f))
                         (error "NUMEX andalso applied to non-boolean")))
                   )
               (error "NUMEX andalso applied to non-boolean")])]

        [(neg? e)
         (let (
               [v1 (eval-under-env (neg-e1 e) env)]
               )
           (cond 
                  [(num? v1) (num (- (num-int v1)))]
                  [(bool? v1) (bool (not (bool-boolean v1)))]
                  [else (error "NUMEX negation applied to non-boolean or non-number")]
                  ))]

        [(cnd? e)
         (let
             (
              [v1 (eval-under-env (cnd-e1 e) env)]
              )
           (cond
             [(equal? v1 (bool #t)) (eval-under-env (cnd-e2 e) env) ]
             [(equal? v1 (bool #f)) (eval-under-env (cnd-e3 e) env) ]
             [(not (bool? v1) ) (error "condition should be boolean")]
             ))]

        [(iseq? e) (
                    let (
                         [v1 (eval-under-env (iseq-e1 e) env)]
                         [v2 (eval-under-env (iseq-e2 e) env)]
                         )
                     (cond
                       [(and (num? v1) (num? v2)) (bool(equal? (num-int v1) (num-int v2)))]
                       [(and (bool? v1) (bool? v2)) (bool (equal? (bool-boolean v1) (bool-boolean v2)))]
                       [else (bool #f)]))]
        
        [(ifnzero? e) (
                    let (
                         [v1 (eval-under-env (ifnzero-e1 e) env)]
                         )
                     (cond
                       [(not (equal? (num-int v1) 0)) (eval-under-env (ifnzero-e2 e) env) ]
                       [else (eval-under-env (ifnzero-e3 e) env)]
                       ))]

        [(ifleq? e) (
                    let (
                         [v1 (eval-under-env (ifleq-e1 e) env)]
                         [v2 (eval-under-env (ifleq-e2 e) env)]
                         )
                     (cond
                       [(> (num-int v1) (num-int v2)) (eval-under-env (ifleq-e4 e) env) ]
                       [else (eval-under-env (ifleq-e3 e) env)]
                       ))]

        [(with? e) (
                    let (
                         [v1 (eval-under-env (with-e1 e) env)]
                         )
                     (eval-under-env (with-e2 e) (cons ( cons (with-s e) v1) env))
                    )]
        [(apply? e) (
                     let (
                          [v1 (eval-under-env (apply-funexp e) env)]
                          )
                      (if (not (closure? v1))
                      ;(if #f
                          (error "you should pass 'funtion' to first part of apply_NUMEX" v1)
                          (let (
                                [v2 (eval-under-env (apply-actual e) env)]
                                )
                            (if (lam? (apply-funexp e))
                                (
                                 if (not (null? (lam-nameopt (apply-funexp e))))
                                    (eval-under-env (lam-body (apply-funexp e)) (merge_two_env (list (cons (lam-formal (apply-funexp e)) v2 ) (cons (lam-nameopt (apply-funexp e)) v1 ))  (closure-env v1)  ))
                                    (eval-under-env (lam-body (apply-funexp e)) (merge_two_env  (list (cons (lam-formal (apply-funexp e)) v2 ))  (closure-env v1)  ))
                                    
                                    )
                                (eval-under-env  (apply (closure-f v1) v2) (merge_two_env  (closure-env v1) env) )

                                            ))))]
        
        [(apair? e) (
                     let (
                          [v1 (eval-under-env (apair-e1 e) env)]
                          [v2 (eval-under-env (apair-e2 e) env)]
                          )
                      (apair v1 v2))]
        
        [(1st? e) (
                   let (
                        [v1 (eval-under-env (1st-e1 e) env)]
                        )
                    (if (apair? v1)
                        (apair-e1 v1)
                        (error "NUMEX 1st applied to non-apair")))]
        
        [(2nd? e) (
                   let (
                        [v (eval-under-env (2nd-e1 e) env)]
                        )
                    (if (apair? v)
                        (apair-e2 v)
                        (error "NUMEX 2nd applied to non-apair")))]

        [(ismunit? e) (
                       let (
                            [v (eval-under-env (ismunit-e e) env)]
                            )
                       (if (munit? v)
                           (bool #t)
                           (bool #f)))]

        [(letrec? e) (
                      let (
                           [v1 (eval-under-env (letrec-e1 e) env)]
                           [v2 (eval-under-env (letrec-e2 e) env)]
                           [v3 (eval-under-env (letrec-e3 e) env)]
                           [v4 (eval-under-env (letrec-e4 e) env)]
                           )
                       (eval-under-env (letrec-e5 e) (merge_two_env (list (cons (letrec-s1 e) v1) (cons (letrec-s2 e) v2) (cons (letrec-s3 e) v3) (cons (letrec-s4 e) v4)) env) )
                       ;(merge_two_env (list (cons (letrec-s1 e) v1) (cons (letrec-s2 e) v2) (cons (letrec-s3 e) v3) (cons (letrec-s4 e) v4)) env)
                       )]
        
        [(key? e) (
                   let (
                        [v (eval-under-env (key-e e) env)]
                        )
                    (cond
                      [(not (string? (key-s e))) (error "first part of key should be string")]
                      [else (key (key-s e) v)]))]
        [(record? e) (
                      let (
                           [k (eval-under-env (record-k e) env)]
                           [r (eval-under-env (record-r e) env)]
                           )
                       (if (key? k)
                           (cond
                             [(or (munit? r) (record? r)) (record k r)]
                             [else (error "second part of record should be munit or record")])
                           (error "first part of record should be key")))]
        [(value? e) (
                     let (
                          [s (eval-under-env (value-s e) env)]
                          [r (eval-under-env (value-r e) env)]
                          )
                      (if (and (string? s) (record? r))
                          (search_value_in_records s r)
                          (error "first part of value_NUMEX should be string and second part of value_NUMEX should be record_NUMEX"))
                      )]
        [(lam? e)
         (closure env e)]
        ;; CHANGE add more cases here
        [(closure? e) e]
        [(munit? e) (munit)]
        [(num? e)
         (cond
           [(integer? (num-int e)) e]
           [else (error "num operate just on integer")]
           )]
        [(string? e) e]
        [(bool? e)
         (cond
           [(boolean? (bool-boolean e)) e]
           [else (error "bool operate just on boolean")]
           )]
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))

;; Problem 3
;; Complete more cases for other kinds of NUMEX expressions.
;; We will test infer-under-env by calling its helper function, infer-exp.
(define (infer-under-env e env)
  (cond [(var? e) 
         (infer-under-env (envlookup env (var-string e)) env)]

        [(plus? e) 
         (let ([t1 (infer-under-env (plus-e1 e) env)]
               [t2 (infer-under-env (plus-e2 e) env)])
           (if (and (equal? "int" t1)
                    (equal? "int" t2))
               "int"
               (error "NUMEX TYPE ERROR: addition applied to non-integer")))]


        [(num? e)
         (cond
           [(integer? (num-int e)) "int"]
           [#t (error "NUMEX TYPE ERROR: num should be a constant number")])]

        [(bool? e)
         (cond
           [(boolean? (bool-boolean e)) "bool"]
           [#t (error "NUMEX TYPE ERROR: bool should be #t or #f")])]

        
        [(minus? e) 
         (let ([t1 (infer-under-env (minus-e1 e) env)]
               [t2 (infer-under-env (minus-e2 e) env)])
           (if (and (equal? "int" t1)
                    (equal? "int" t2))
               "int"
               (error "NUMEX TYPE ERROR: subtraction applied to non-integer")))]
        [(mult? e) 
         (let ([t1 (infer-under-env (mult-e1 e) env)]
               [t2 (infer-under-env (mult-e2 e) env)])
           (if (and (equal? "int" t1)
                    (equal? "int" t2))
               "int"
               (error "NUMEX TYPE ERROR: multiplication applied to non-integer")))]

        [(div? e) 
         (let ([t1 (infer-under-env (div-e1 e) env)]
               [t2 (infer-under-env (div-e2 e) env)])
           (if (and (equal? "int" t1)
                    (equal? "int" t2))
               "int"
               (error "NUMEX TYPE ERROR: division applied to non-integer")))]
        [(andalso? e) 
         (let ([t1 (infer-under-env (andalso-e1 e) env)]
               [t2 (infer-under-env (andalso-e2 e) env)])
           (if (and (equal? "bool" t1)
                    (equal? "bool" t2))
               "bool"
               (error "NUMEX TYPE ERROR: andalso applied to non-boolean")))]
        [(orelse? e) 
         (let ([t1 (infer-under-env (orelse-e1 e) env)]
               [t2 (infer-under-env (orelse-e2 e) env)])
           (if (and (equal? "bool" t1)
                    (equal? "bool" t2))
               "bool"
               (error "NUMEX TYPE ERROR: orelse applied to non-boolean")))]
        
        [(neg? e)
         (let ([t (infer-under-env (neg-e1 e) env) ])
           (cond
           [(equal? "null" t) (error "NUMEX TYPE ERROR: negation of null type is incorrect" )]
           [else t]
           )
         )]
        [(cnd? e)
         ( let (
                [t1 (infer-under-env (cnd-e1 e) env)]
                )
            (if (equal? "bool" t1)
                (let (
                      [t2 (infer-under-env (cnd-e2 e) env)]
                      [t3 (infer-under-env (cnd-e3 e) env)]
                      )
                  (if (equal? t2 t3)
                      t2
                      (error "NUMEX TYPE ERROR: second and third part of cnd should be the same") ))
                (error "NUMEX TYPE ERROR: first part of cnd is non-boolean")))
         ]
        [(iseq? e)
         (let (
               [t1 (infer-under-env (iseq-e1 e) env)]
               [t2 (infer-under-env (iseq-e2 e) env)]        
               )
           (if (equal? t1 t2)
               "bool"
                (error "NUMEX TYPE ERROR: first and second part of iseq should be the same")
                ))]
        [(with? e)
         (
          let (
               [t1 (infer-under-env (with-e1 e) env)]
               ;(eval-under-env (with-e2 e) (cons ( cons (with-s e) v1) env))
               )
           (infer-under-env (with-e2 e) (cons ( cons (with-s e) t1) env))
          )]
        [(apply? e)
         (let (
               [t_funexp (infer-under-env (apply-funexp e) env)]
               [t_actual (infer-under-env (apply-actual e) env)]
               ;(struct function (input-type output-type) #:transparent) ;; e.g. (function ("int" int")) means fn f "int" -> "int"
               ;(struct tlam  (nameopt formal arg-type body) #:transparent) ;; a typed argument, recursive(?) 1-argument function
               ;(struct apply (funexp actual)       #:transparent) ;; function application
               )
           (if (and (function? t_funexp) (equal? (function-input-type t_funexp) t_actual ))
               (function-output-type t_funexp)
               (error "NUMEX TYPE ERROR: apply type error")))]

        [(tlam? e) ( let (
                          [t_out (infer-under-env (tlam-body e) (cons (cons (tlam-formal e) (tlam-arg-type e)) env) ) ]
                          )
                    (function (tlam-arg-type e) t_out) 
                    )]

        ;(struct collection (type) #:transparent) ;; collection of a certain type, e.g., (collection "int")
        [(apair? e) (
                     let (
                          [t1 (infer-under-env (apair-e1 e) env)]
                          [t2 (infer-under-env (apair-e2 e) env)]
                          )
                      (cond
                        [(equal? "null" t2) (collection t1)]
                        [(collection? t2)
                         (if (equal? (collection-type t2) t1)
                             t2
                             (error "NUMEX TYPE ERROR: apair type error"))]
                        [else (error "NUMEX TYPE ERROR: apair type error")]

                        ))]
        [(1st? e)
         (let (
               [t1 (infer-under-env (1st-e1 e) env)]
               )
           (
            if (collection? t1) (collection-type t1) (error "NUMEX TYPE ERROR: 1st should operate on collection")
            ))]
        [(2nd? e)
         (let (
               [t2 (infer-under-env (2nd-e1 e) env)]
               )
           (
            if (collection? t2) t2 (error "NUMEX TYPE ERROR: 2nd should operate on collection")
            ))]
        [(ismunit? e)
         (let ([t1 (infer-under-env (ismunit-e e) env)])
           (
            if (or (collection? t1) (equal? "null" t1)) "bool" (error "NUMEX TYPE ERROR: ismunit should operate on collection type" )
            ))]
        ;; CHANGE add more cases here
        [(munit? e) "null"]
        [(string? e) e]
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (infer-exp e)
  (infer-under-env e null))

;; Problem 4

(define (ifmunit e1 e2 e3) 
                             (cnd (ismunit e1) e2 e3)
                            )

(define (with* bs e2)
  (
   cond
    [(null? bs) e2]
    [else (with (car (car bs)) (cdr (car bs)) (with* (cdr bs) e2 ) )]
   )
  )

(define (ifneq e1 e2 e3 e4)
  (cnd (neg (iseq e1 e2)) e3 e4)
  )

;; Problem 5
(define numex-filter
  (lam null "f"
       (lam "H" "lst"
            (cnd (ismunit (var "lst"))
                 (var "lst")
                 (with "element" (apply (var "f") (1st (var "lst")))
                       (
                        cnd (iseq (var "element") (num 0))
                            (apply (var "H") (2nd (var "lst")))
                            (apair (var "element") (apply (var "H") (2nd (var "lst"))) )
                        )
                       )
              )
            )
       ))
(define numex-all-gt
  (with "filter" numex-filter
  (lam null "n"
        (apply
         (var "filter")
         (lam null "x"
              (ifleq (var "x") (var "n")
                     (num 0)
                     (var "x")))
         )
         
  )))


;; Problem 6

(define type-error-but-evaluates-ok (cnd (bool #t) (num 20) (bool #f)))
(define type-ok-but-evaluates-error "CHANGE")

; (var "n")


(eval-exp (
           lam "f" "x" (cnd #t #t #t)
           ))


;(eval-exp
;                  (apply (apply numex-all-gt (num 1) )
;                   (apair (num 2) (apair (num 1) (apair (num -2) (munit))))))


;(eval-exp
;                  (apply (apply numex-all-gt (num 2) )
;                   (apair (num 2) (apair (neg (num 2)) (apair (num -2) (munit))))))
;(eval-exp
;     (with "range"
;           (lam "range" "lo"
;                (lam null "hi"
;                     (ifleq  (var "hi") (var "lo") (munit)
;                                (apair (var "lo") (apply (apply (var "range") (plus (num 1) (var "lo"))) (var "hi"))))))
;           (apply (apply (var "range") (num 5)) (num 8))))

;(eval-exp (apply (lam "fact" "n" 
   ;        (cnd (iseq (var "n") (num 0)) 
   ;                (num 1) 
   ;                (mult (var "n") (apply (var "fact") (minus (var "n") (num 1))
   ;        )))) (num 20)))
                   
;(eval-exp
 ;                 (apply (apply numex-filter (lam null "x" (plus (num 1) (var "x"))))
  ;                 (apair (num 1) (apair (num 2) (munit)))))

;(eval-exp (with* (list (cons "x" (num 1)) (cons "y" (num 2))) (plus (var "x")(var "y"))))
;(closure
; (list (cons "f" (closure '() (lam '() "x" (plus (num 1) (var "x"))))))
; (lam "H" "lst" (cnd (ismunit (var "lst")) (var "lst") (apair (apply (var "f") (1st (var "lst"))) (apply (var "H") (2nd (var "lst")))))))

;(eval-exp
;                  (apply
;                   (closure
; (list (cons "f" (closure '() (lam '() "x" (plus (num 1) (var "x"))))))
; (lam "H" "lst" (cnd (ismunit (var "lst")) (var "lst") (apair (apply (var "f") (1st (var "lst"))) (apply (var "H") (2nd (var "lst")))))))
 ;                  (apair (num 1) (apair (num 2) (munit)))))


















;(eval-exp (with* (list (cons "f" (num 2)) (cons "y" (var "f"))) (plus (var "f") (plus (var "y") (num 3)))))
;(eval-exp (with* (cons (cons "x" (num 1)) null) (var "x")))
;(eval-exp (ifneq (num 1) (num 2) (num 3) (num 4) ))
;(eval-exp (ifneq (num 1) (num 1) (num 3) (bool #t)))
;(eval-exp (ifmunit (munit) (plus (num 1) (num 2)) (plus (num 3)(num 4))))
;(infer-exp (plus (num 2) (num 5)))
;(infer-exp (minus (num 20) (num 5)))
;(infer-exp (mult (num 20) (num 5)))
;(infer-exp (div (num 21) (num 5)))

;(infer-exp (bool #t))
;(infer-exp (neg (num 5)))
;(infer-exp (tlam "f" "x" "int" (plus (num 2) (var "x"))))

;(infer-exp (tlam "f" "x" "bool" (andalso (bool #f) (var "x"))))

;(infer-exp (apply (tlam "f" "x" "int" (plus (var "x") (num 3))) (num 4)))
;(infer-exp (apply (tlam "f" "x" "int" (plus (var "x") (num 3))) (bool #t)))
;(infer-exp (apair (num 1) (apair (num 2) (munit))))

;(infer-exp (apair (bool #t) (apair (bool #t) (munit))))
;(infer-exp (munit))
;(infer-exp (ismunit (munit)))





;(eval-exp (minus (num 200) (num 2)))
;(eval-exp (andalso (bool #f) "s"))
;(eval-exp (num 17))
;(eval-exp (bool #t))
;(envlookup (list (cons "a" 1) (cons "b" 3)) "a")
;(eval-exp (orelse (bool #f) (bool #f)))
;(eval-exp (neg (num -500)))
;(eval-exp (neg "s"))
;(eval-exp (cnd (bool #f) (minus (num 200) (num 2)) (num 17)))
;(eval-exp (iseq (num 20) (num 19)))
;(eval-exp (iseq (bool #t) (bool #t)))
;(eval-exp (ifnzero (minus (num 200) (num 200)) (bool #t) (bool #f)))
;(eval-exp (with "x" (num 20) (var "x")))
;(eval-exp (iseq (num 2) (num -2)))
;(eval-exp (2nd(apair (plus (num 1) (num 20)) (mult (num 1) (num 20)) )))
;(eval-exp (ismunit (num 5)))

;(envlookup (merge_two_env (list (cons "a" 1) (cons "b" 3)) (list (cons "d" 1) (cons "e" 3) )) "a")

;(merge_two_env (list (cons "a" 1) (cons "b" 3)) (list (cons "d" 1) (cons "e" 3) ))
;(eval-exp (key "1" (plus (num 1) (num 2))))
;(eval-exp (value "Donald Knuth" (record (key "Donald Knuth" (num 1)) (record (key "John McCarthy" (num 2)) (record (key "Barbara Liskov" (num 3)) (munit))))))

;(search_value_in_records "Donald Knuth" (record (key "Donald Knuth" (num 1)) (record (key "John McCarthy" (num 2)) (record (key "Barbara Liskov" (num 3)) (munit)))))
;(apply (eval-exp (lam null "x" (var "x")))
;(eval-exp (with "x" (num 1) (lam null "a" (var "x"))))
;(eval-exp (apply (lam "a" "b" (ifleq (var "b") (num 5) (plus (var "b") (num 3))
 ;                                                     (apply (var "a") (mult (num 2) (num 3)))))
  ;                                (num 2)))
;(eval-exp (apply (lam "incr" "x" (plus (var "x") (num 1))) (num 42)))
;(eval-exp (lam "incr" "x" (plus (var "x") (num 1))))
;(eval-exp (apply (lam "mul" "x" (neg (mult (var "x") (num 2)))) (num -5)))
;(eval-exp (apply (apply (apply (lam "a" "b" (lam "x" "y" (lam "w" "r" (neg (mult (plus (var "b") (var "y")) (var "r"))))))
;                       (num 2))
;                       (num 3))
;                       (num 5))
           ; )
;(eval-exp (letrec
;              "is-even" (lam null "n" (orelse (iseq (var "n") (num 0)) (apply (var "is-odd") (minus (var "n") (num 1)))))
;            "is-odd" (lam null "n" (andalso (neg (iseq (var "n") (num 0))) (apply (var "is-even") (minus (var "n") (num 1)))))
;            "temporary-1" (num 1)
;            "temporary-2" (num 2)
;            (apply (var "is-odd") (num 9))))

;(eval-exp (apply (lam "a" "b" (ifnzero (var "b") 
 ;                                     (with* (list (cons "b" (plus (var "b") (num -1)))) (plus (num 1) (apply (var "a") (var "b"))))
 ;                                     (num 3)
 ;                                     )) (num 2))
 ;            )

;(eval-exp (apply (apply (apply (lam "a" "b" (lam "x" "y" (lam "w" "r" (neg (mult (plus (var "b") (var "y")) (var "r"))))))
;                       (num 2))
;                       (num 3))
;                       (num 5))
 ;           )



;(eval-exp (letrec "is-even" (lam null "n" (orelse (iseq (var "n") (num 0)) (apply (var "is-odd") (minus (var "n") (num 1))))) "is-odd" (lam null "n" (andalso (neg (iseq (var "n") (num 0))) (apply (var "is-even") (minus (var "n") (num 1))))) "temporary-1" (num 1) "temporary-2" (num 2) (apply (var "is-odd") (num 11))))



;(eval-exp (with "fnc"
;       (lam "f1" "x" 
;            (ifneq (ismunit (var "x")) (bool #f) 
;                       (num 0) 
;                       (plus (1st (var "x")) (apply (var "f1") (2nd (var "x"))))))
;       (apply (var "fnc") (apair (num 1) (apair (num 2) (apair (num 3) (munit)))))))