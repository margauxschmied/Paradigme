; Cours 10 : Types

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (par-type : Type) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [boolE (b : Boolean)]
  [ifE (cnd : Exp) (e1 : Exp) (e2 : Exp)]
  [equE (e1 : Exp) (e2 : Exp)]
  [pairE (f : Exp) (s : Exp)] 
  [fstE (e : Exp)]
  [sndE (e : Exp)]
  [letrecE (s : Symbol) (t : Type) (body : Exp) (rhs : Exp)]) 

; Représentation du type des expressions
(define-type Type
  [numT]
  [boolT]
  [arrowT (par : Type) (res : Type)]  
  [prodT (l : Type) (r : Type)]
  [varT (is : (Boxof (Optionof Type)))])
   
; Représentation des liaisons identificateurs type 
(define-type TypeBinding
  [tbind (name : Symbol) (type : Type)])

; Environnement pour les types
(define-type-alias TypeEnv (Listof TypeBinding))

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [boolV (b : Boolean)]
  [pairV (f : Value) (s : Value)]
  [closV (arg : Symbol) (body : Exp) (env : Env)]
  [undefV]) 

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : (Boxof Value))])
  

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding)) 
(define mt-env empty)
(define extend-env cons)

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp 
  (cond
    [(s-exp-match? `true s) (boolE #true)]
    [(s-exp-match? `false s) (boolE #false)]
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]

    [(s-exp-match? `{letrec {[SYMBOL : ANY ANY]} ANY} s) 
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (letrecE (s-exp->symbol (first sll)) 
                  (parse-type (third sll))
                  (parse (third sl))
                  (parse (fourth sll)))))] 
    ;[letrecE (s : Symbol) (t : Type) (body : Exp) (rhs : Exp)]
         
 
    [(s-exp-match? `{pair ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (pairE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{fst ANY} s)
     (let ([sl (s-exp->list s)])
       (fstE (parse (second sl))))] 
    [(s-exp-match? `{snd ANY} s)
     (let ([sl (s-exp->list s)])
       (sndE (parse (second sl))))] 
    
    [(s-exp-match? `{= ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (equE (parse (second sl)) (parse (third sl))))] 
    [(s-exp-match? `{if ANY ANY ANY} s) 
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {[SYMBOL : ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (lamE (s-exp->symbol (first sll))
               (parse-type (third sll))
               (parse (third sl)))))]
    [(s-exp-match? `{let {[SYMBOL : ANY ANY]} ANY} s) 
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (first (s-exp->list (second sl))))])
         (appE
          (lamE (s-exp->symbol (first sll))
                (parse-type (third sll))
                (parse (third sl)))
          (parse (fourth sll)))))]
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

(define (parse-type [s : S-Exp]) : Type 
  (cond
    [(s-exp-match? `num s) (numT)]
    [(s-exp-match? `bool s) (boolT)]
    [(s-exp-match? `? s) (varT (box (none)))]
    [(s-exp-match? `(ANY -> ANY) s)
     (let ([sl (s-exp->list s)]) 
       (arrowT (parse-type (first sl))
               (parse-type (third sl))))]
    [(s-exp-match? `(ANY * ANY) s)
     (let ([sl (s-exp->list s)])
       (prodT (parse-type (first sl)) (parse-type (third sl))))]
    [else (error 'parse "invalid input")])) 

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Vérification des types ;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (typecheck [e : Exp] [env : TypeEnv]) : Type 
  (type-case Exp e
    [(numE n) (numT)]
    [(idE s) (type-lookup s env)]
    [(plusE l r) (typecheck-op l r env)]
    [(multE l r) (typecheck-op l r env)]
    [(lamE par par-type body)
     (arrowT par-type
             (typecheck body
                        (extend-env (tbind par par-type) env)))]
    [(appE fun arg) 
     (let ([t1 (varT (box (none)))]
           [t2 (varT (box (none)))])
       (begin
         (unify! (typecheck fun env) (arrowT t1 t2) fun)
         (unify! (typecheck arg env) t1 arg)
         t2))]
    [(boolE b) (boolT)]
    [(equE e1 e2)
     (let ([t1 (typecheck e1 env)]
           [t2 (typecheck e2 env)]) 
       (begin
         (unify! t1 (numT) e1)
         (unify! t2 (numT) e2)
         (boolT) 
         ))]  
    
    [(ifE cnd e1 e2) 
     (let ([c (typecheck cnd env)]
           [t1 (typecheck e1 env)]
           [t2 (typecheck e2 env)])
       (begin
         (unify! c (boolT) cnd)  
         (unify! t2 t1 e2) 
         t1 
         ))]
    [(pairE f s) (let ([t1 (typecheck f env)]
                       [t2 (typecheck s env)])
                   (begin
                     (unify! (varT (box (none))) t1 f)
                     (unify! (varT (box (none))) t2 s)
                     (prodT (resolve t1) (resolve t2))))]
    [(fstE e)
     (let ([p (typecheck e env)])  
       (begin
         (unify! p (prodT (varT (box (none))) (varT (box (none)))) e)
         (prodT-l (resolve p)))     
       )]    
    [(sndE e) 
     (let ([p (typecheck e env)])     
       (begin
         (unify! p (prodT (varT (box (none))) (varT (box (none)))) e)
         (prodT-r (resolve p))))]
    [(letrecE s t body rhs) 
     (let ([env2 (extend-env (tbind s t) env)])
       (let ([t1 (typecheck rhs env2)]
             [t2 (typecheck body env2)])   
         (begin
           (unify! t t1 body)
           t2)                 
         ))]        
    ))   

; spécialisation de typecheck pour les opérateurs arithmétiques
(define (typecheck-op [l : Exp] [r : Exp] [env : TypeEnv]) : Type
  (begin
    (unify! (typecheck l env) (numT) l)
    (unify! (typecheck r env) (numT) r)  
    (numT)))

; Concaténation de chaînes de caractères
(define (cat [strings : (Listof String)]) : String
  (foldr string-append "" strings))

; Message d'erreur
(define (type-error [expr : Exp] [expected-type : Type] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected type " (to-string expected-type)
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-function [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected function " 
                               ", found type " (to-string found-type)))))

; Message d'erreur
(define (type-error-product [expr : Exp] [found-type : Type])
  (error 'typecheck (cat (list "expression " (to-string  expr)
                               ", expected product "
                               ", found type " (to-string found-type)))))

; Recherche d'un identificateur dans l'environnement
(define (type-lookup [s : Symbol] [env : TypeEnv]) : Type
  (cond
    [(empty? env) (error 'typecheck "free identifier")]
    [(equal? s (tbind-name (first env))) (tbind-type (first env))]
    [else (type-lookup s (rest env))]))

;;;;;;;;;;;;;;;;;;
; Interprétation ; 
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(idE s) (lookup s env)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))] 
    [(lamE par par-type body) (closV par body env)]
    
    [(appE f arg)
     (type-case Value (interp f env) 
       [(closV par body c-env)
        (interp body (extend-env (bind par (box (interp arg env))) c-env))]
       ;(interp body (extend-env (bind par (interp arg env)) c-env))]
       [else (begin (display (interp f env)) (error 'interp "not a function"))])]
    [(boolE b) (boolV b)]
    [(equE l r) (num= (interp l env) (interp r env))]                       
    [(ifE q f s) (num-if q f s env)]
    [(pairE f s) (pairV (interp f env) (interp s env))] 
    [(fstE e) (type-case Value (interp e env)
                [(pairV f s) f] 
                [else (error 'interp "not a pair")])]  
    [(sndE e) (type-case Value (interp e env)
                [(pairV f s) s]
                [else (error 'interp "not a pair")])]
    [(letrecE s t body rhs)
     (let ([b (box (undefV))])
       (let ([new-env (extend-env (bind s b) env)]) 
         (begin
           (set-box! b (interp rhs new-env)) 
           (interp body new-env))))]))  

(define (num= [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (boolV (= (numV-n l) (numV-n r)))
      (error 'interp "not a number"))) 
 
(define (num-if [b : Exp]
                [f : Exp] [s : Exp] [e : Env]) : Value   
  (if (boolV? (interp b e))
      (if (boolV-b (interp b e)) 
          (interp f e) 
          (interp s e))  
      (error 'interp "not a boolean")))


; Recherche d'un identificateur dans l'environnement
(define (lookup [s : Symbol]
                [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) (unbox (bind-val (first env)))]
    [else (lookup s (rest env))]))

; Vérification des types pour les opérations arithmétiques
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

; Spécialisation de num-op pour l'addition
(define (num+ [l : Value] [r : Value]) : Value 
  (num-op + l r))

; Spécialisation de num-op pour la multiplication
(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

; unification de deux types
(define (unify! [t1 : Type] [t2 : Type] [e : Exp]) : Void
  (type-case Type t1 
    [(varT is1)
     (type-case (Optionof Type) (unbox is1)
       [(some t3) (unify! t3 t2 e)]
       [(none)
        (let ([t3 (resolve t2)])
          (cond
            [(eq? t1 t3) (void)]
            [(occurs t1 t3) (type-error e t1 t3)]
            [else (set-box! is1 (some t3))]))])]
    [else
     (type-case Type t2
       [(varT is2) (unify! t2 t1 e)]
       [(arrowT t3 t4)
        (type-case Type t1
          [(arrowT t5 t6)
           (begin
             (unify! t3 t5 e)
             (unify! t4 t6 e))]
          [else (type-error e t1 t2)])]
       [(prodT t3 t4)
        (type-case Type t1
          [(prodT t5 t6)
           (begin
             (unify! t3 t5 e)
             (unify! t4 t6 e))]
          [else (type-error e t1 t2)])]
       [else
        (if (equal? t1 t2)
            (void)
            (type-error e t1 t2))])]))

; résolution d'une variable (descente dans les alias)
(define (resolve [t : Type]) : Type
  (type-case Type t
    [(varT is)
     (type-case (Optionof Type) (unbox is)
       [(none) t]
       [(some t2) (resolve t2)])]
    [(arrowT t1 t2) (arrowT (resolve t1) (resolve t2))]
    [(prodT t1 t2) (prodT (resolve t1) (resolve t2))]
    [else t]))

; test de l'apparition de la variable t1 dans le type t2
(define (occurs [t1 : Type] [t2 : Type]) : Boolean
  (type-case Type t2
    [(arrowT t3 t4) (or (occurs t1 t3) (occurs t1 t4))]
    [(prodT t3 t4) (or (occurs t1 t3) (occurs t1 t4))]
    [(varT is)
     (or (eq? t1 t2)
         (type-case (Optionof Type) (unbox is)
           [(none) #f]
           [(some t3) (occurs t1 t3)]))] 
    [else #f])) 

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (let ([expr (parse e)])
    (begin
      (typecheck expr mt-env)
      (interp expr mt-env))))

(define (typecheck-expr [e : S-Exp]) : Type
  (resolve (typecheck (parse e) mt-env)))

(test (typecheck-expr `{= 1 2}) (boolT))
(test (typecheck-expr `{if {= 1 2} true false}) (boolT))
(test/exn (typecheck-expr `{if 1 2 3}) "typecheck")

(test (typecheck-expr `{pair 1 true}) (prodT (numT) (boolT))) (test (typecheck-expr `{fst {pair 1 true}}) (numT))
(test (typecheck-expr `{snd {pair 1 true}}) (boolT))
(test (typecheck-expr `{lambda {[x : (num * bool)]} {fst x}})
      (arrowT (prodT (numT) (boolT)) (numT)))

(test (typecheck-expr
       `{letrec {[fib : (num -> num) 
                      {lambda {[n : num]} {if {= n 0}
                                              0
                                              {if {= n 1}
                                                  1
                                                  {+{fib {+ n -2}}
                                                    {fib {+ n -1}}}}}}]}
          {fib 6}}) (numT))

(test/exn (typecheck-expr `{let {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) "typecheck")
(test (typecheck-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numT)) 

 
(test (interp-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numV 0))



(test (typecheck-expr `{let {[f : ? {lambda {[x : ?]} x}]}
                         {let {[x : ? {f 1}]}
                           f}})
      (arrowT (numT) (numT)))

(test (typecheck-expr `{letrec {[fib : ? 
                                     {lambda {[n : ?]} {if {= n 0}
                                                           0
                                                           {if {= n 1}
                                                               1
                                                               {+ {fib {+ n -2}}
                                                                  {fib {+ n -1}}}}}}]}
                         {fib 6}}) (numT))


(test (typecheck-expr `{lambda {[x : ?]} {if x 1 2}}) (arrowT (boolT) (numT)))

(test (typecheck-expr `{let {[apply-fun : (bool -> (num -> num))
                                        {lambda {[x : bool]}
                                          {if x
                                              {lambda {[x : num]} {+ x 1}}
                                              {lambda {[x : num]} {* x 2}}}}]}
                         {{apply-fun true} 3}})
      (numT))

(test (typecheck-expr `{lambda {[x : ?]} {if x x false}}) (arrowT (boolT) (boolT)))

(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})
      (arrowT (prodT (boolT) (numT)) (numT)))

( test ( interp-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 20} })
       (numV 6765))


( test/exn ( typecheck-expr `{ fst 2 }) 
           "typecheck")

( test/exn ( typecheck-expr `{ snd 5 })
           "typecheck")

( test/exn ( typecheck-expr `(= 1 (= 1 2)))
           "typecheck")

( test ( interp-expr `{ if {= 1 2} true false })
       (boolV #f))
( test/exn ( interp-expr `{ if 1 2 3})
           "typecheck")
( test ( interp-expr `{ pair 1 true }) (pairV (numV 1) (boolV #t)))
( test ( interp-expr `{ fst { pair 1 true } }) (numV 1))
( test ( interp-expr `{ snd { pair 1 true } }) (boolV #t))
( test ( typecheck-expr `{ lambda {[x : (num * bool )]} { fst x} })
       ( arrowT ( prodT ( numT ) ( boolT )) ( numT )))
( test ( interp-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       (numV 8))
(test/exn (interp-expr `{let {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) "typecheck")
(test (interp-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numV 0))
( test ( typecheck-expr `{ let {[f : ? { lambda {[x : ?]} x}]}
                            { let {[x : ? {f 1}]}
                               f} })
       ( arrowT ( numT ) ( numT )))

( test ( interp-expr
         `{ letrec {[fib : ?
                         { lambda {[n : ?]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 6} })
       (numV 8))
(test (typecheck-expr `{lambda {[x : ?]} {if x 1 2}}) (arrowT (boolT) (numT)))
(test (interp-expr `{let {[apply-fun : (bool -> (num -> num))
                                     {lambda {[x : bool]}
                                       {if x
                                           {lambda {[x : num]} {+ x 1}}
                                           {lambda {[x : num]} {* x 2}}}}]}
                      {{apply-fun true} 3}})
      (numV 4))
(test (typecheck-expr `{lambda {[x : ?]} {if x x false}}) (arrowT (boolT) (boolT)))
(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})
      (arrowT (prodT (boolT) (numT)) (numT)))
( test ( interp-expr
         `{ letrec {[fib : (num -> num)
                         { lambda {[n : num]}
                            { if {= n 0}
                                 0
                                 { if {= n 1}
                                      1
                                      {+ { fib {+ n -2} }
                                         { fib {+ n -1} } } } } }]}
             { fib 20} })
       (numV 6765))
( test/exn ( interp-expr `{ fst 2 })
           "typecheck")

( test/exn ( typecheck-expr `{ snd 5 })
           "typecheck")
( test/exn ( interp-expr `{= 1 {= 3 2}})
           "typecheck")
( test/exn ( interp-expr `{= 1 false})
           "typecheck")
( test/exn ( interp-expr `{= true false})
           "typecheck")

(test (interp-expr `{let {[f : ?
                             {lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}}]}
                      {f {pair false 3}}})
      (numV 4))



( test ( typecheck-expr `{ if {= 1 2} true false })

       ( boolT ))





( test/exn ( typecheck-expr `{ if 1 2 3})

           "typecheck")



( test/exn ( typecheck-expr `{= 1 {= 3 2}})

           "typecheck")

( test ( typecheck-expr `{ pair 1 true }) ( prodT ( numT ) ( boolT )))

( test ( typecheck-expr `{ fst { pair 1 true } }) ( numT ))

( test ( typecheck-expr `{ snd { pair 1 true } }) ( boolT ))

( test ( typecheck-expr `{ lambda {[x : (num * bool )]} { fst x} })

       ( arrowT ( prodT ( numT ) ( boolT )) ( numT )))

(parse `{ lambda {[x : (num * bool )]} { fst x}})

( test ( typecheck-expr `{ lambda {[x : (num * num )]} {  if true true false} })

       ( arrowT ( prodT ( numT ) ( numT )) ( boolT )))

(parse `{letrec {[x : num x]} x})

(test/exn (typecheck-expr `{let {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) "typecheck")

(test (typecheck-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numT))





(parse `{letrec {[x : (num -> num) x]} x})

(test (typecheck-expr

       `{letrec {[fib : (num -> num)

                      {lambda {[n : num]} {if {= n 0}

                                              0

                                              {if {= n 1} 1

                                                  {+{fib {+ n -2}}

                                                    {fib {+ n -1}}}}}}]}

          {fib 6}}) (numT))

( test ( typecheck-expr `{ let {[f : ? { lambda {[x : ?]} x}]}

                            { let {[x : ? {f 1}]}

                               f} })

       ( arrowT ( numT ) ( numT )))

( test ( typecheck-expr

         `{ letrec {[fib : ?

                         { lambda {[n : ?]}

                            { if {= n 0}

                                 0

                                 { if {= n 1}

                                      1

                                      {+ { fib {+ n -2} }

                                         { fib {+ n -1} } } } } }]}

             { fib 6} })

       ( numT ))





(test (typecheck-expr `{let {[apply-fun : (bool -> (num -> num))

                                        {lambda {[x : bool]}

                                          {if x

                                              {lambda {[x : num]} {+ x 1}}

                                              {lambda {[x : num]} {* x 2}}}}]}

                         {{apply-fun true} 3}})

      (numT))





(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})

      (arrowT (prodT (boolT) (numT)) (numT)))



( test/exn ( typecheck-expr `{ if true 2 false})

           "typecheck")



( test/exn ( typecheck-expr `{ fst 2 })

           "typecheck")



( test/exn ( typecheck-expr `{ snd 5 })

           "typecheck")



( test ( interp-expr

         `{ letrec {[fib : (num -> num)

                         { lambda {[n : num]}

                            { if {= n 0}

                                 0

                                 { if {= n 1}

                                      1

                                      {+ { fib {+ n -2} }

                                         { fib {+ n -1} } } } } }]}

             { fib 20} })

       (numV 6765))







 



(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})

      (arrowT (prodT (boolT) (numT)) (numT)))









(test (interp-expr `{let {[f : ?

                             {lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}}]}

                      {f {pair false 3}}})

      (numV 4))



( test/exn ( interp-expr `{= true false})

           "typecheck")

( test/exn ( typecheck-expr `{= 1 false})

           "typecheck")

(test (interp-expr `{ = 1  1 } ) (numV 1))

( test/exn ( interp-expr `{ snd 5 })

           "typecheck")





( test ( interp-expr `{ if {= 1 2} true false })

       (numV 0))

( test/exn ( interp-expr `{ if 1 2 3})

           "typecheck")

( test ( interp-expr `{ pair 1 true }) (pairV (numV 1) (numV 1)))

( test ( interp-expr `{ fst { pair 1 true } }) (numV 1))

( test ( interp-expr `{ snd { pair 1 true } }) (numV 1))

( test ( typecheck-expr `{ lambda {[x : (num * bool )]} { fst x} })

       ( arrowT ( prodT ( numT ) ( boolT )) ( numT )))

( test ( interp-expr

         `{ letrec {[fib : (num -> num)

                         { lambda {[n : num]}

                            { if {= n 0}

                                 0

                                 { if {= n 1}

                                      1

                                      {+ { fib {+ n -2} }

                                         { fib {+ n -1} } } } } }]}

             { fib 6} })

       (numV 8))

(test/exn (interp-expr `{let {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) "typecheck")

(test (interp-expr `{letrec {[f : (num -> num) {lambda {[x : num]} {f x}}]} 0}) (numV 0))

( test ( typecheck-expr `{ let {[f : ? { lambda {[x : ?]} x}]}

                            { let {[x : ? {f 1}]}

                               f} })

       ( arrowT ( numT ) ( numT )))



( test ( interp-expr

         `{ letrec {[fib : ?

                         { lambda {[n : ?]}

                            { if {= n 0}

                                 0

                                 { if {= n 1}

                                      1

                                      {+ { fib {+ n -2} }

                                         { fib {+ n -1} } } } } }]}

             { fib 6} })

       (numV 8))

(test (typecheck-expr `{lambda {[x : ?]} {if x 1 2}}) (arrowT (boolT) (numT)))

(test (interp-expr `{let {[apply-fun : (bool -> (num -> num))

                                        {lambda {[x : bool]}

                                          {if x

                                              {lambda {[x : num]} {+ x 1}}

                                              {lambda {[x : num]} {* x 2}}}}]}

                         {{apply-fun true} 3}})

      (numV 4))

(test (typecheck-expr `{lambda {[x : ?]} {if x x false}}) (arrowT (boolT) (boolT)))

(test (typecheck-expr `{lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}})

      (arrowT (prodT (boolT) (numT)) (numT)))

( test ( interp-expr

         `{ letrec {[fib : (num -> num)

                         { lambda {[n : num]}

                            { if {= n 0}

                                 0

                                 { if {= n 1}

                                      1

                                      {+ { fib {+ n -2} }

                                         { fib {+ n -1} } } } } }]}

             { fib 20} })

       (numV 6765))

( test/exn ( interp-expr `{ fst 2 })

           "typecheck")



( test/exn ( typecheck-expr `{ snd 5 })

           "typecheck")

( test/exn ( interp-expr `{= 1 {= 3 2}})

           "typecheck")

( test/exn ( interp-expr `{= 1 false})

           "typecheck")

( test/exn ( interp-expr `{= true false})

           "typecheck")



(test (interp-expr `{let {[f : ?

                             {lambda {[p : ?]} {if {fst p} {snd p} {+ 1 {snd p}}}}]}

                      {f {pair false 3}}})

      (numV 4))

(test/exn (typecheck-expr `{letrec {[x : num true]} {+ x 1}}) "typecheck")

(test (typecheck-expr `{letrec {[even : ?
                                      {lambda {[n : ?]}
                                        {if {= n 0}
                                            true
                                            {if {= n 1}
                                                false
                                                {even {+ n -2}}}}}]}
                         {letrec {[div2 : ?
                                        {lambda {[n : ?]}
                                          {if {= n 0}
                                              0
                                              {if {= n 1}
                                                  0
                                                  {+ 1 {div2 {+ n -2}}}}}}]}
                           {letrec {[syracuse : ?
                                              {lambda {[n : ?]}
                                                {if {= n 1}
                                                    true
                                                    {if {even n}
                                                        {syracuse {div2 n}}
                                                        {syracuse {+ {* 3 n} 1}}}}}]}
                             {syracuse 3}}}})
      (boolT))

(test/exn (typecheck-expr `{letrec {[f : ?
                                       {lambda {[p : ?]}
                                         {if {fst p}
                                             0
                                             {f {snd p}}}}]}
                             f})
          "typecheck") 