; Cours 04 : Les boîtes avec macro simplificatrice

#lang plait

;;;;;;;;;
; Macro ;
;;;;;;;;;

(define-syntax-rule (with [(v-id sto-id) call] body)
  (type-case Result call
    [(v*s v-id sto-id) body]))

;;;;;;;;;;;;;;;;;;;;;;;;  
; Définition des types ; 
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [letE (s : Symbol) (rhs : Exp) (body : Exp)]
  [boxE (val : Exp)] 
  [unboxE (b : Exp)]
  [setboxE (b : Exp) (val : Exp)]
  [beginE (l : Exp) (r : (Listof Exp))]
  [recordE (s : (Listof Symbol)) (e : (Listof Exp))]
  [getE (e : Exp) (s : Symbol)]
  [setE (e : Exp) (s : Symbol) (e2 : Exp)])
  

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [boxV (l : Location)]
  [recV (fields : (Listof Symbol)) (vals : (Listof Location))])

; Représentation du résultat d'une évaluation
(define-type Result
  [v*s (v : Value) (s : Store)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des adresses mémoire
(define-type-alias Location Number)

; Représentation d'un enregistrement
(define-type Storage
  [cell (location : Location) (val : Value)])

; Manipulation de la mémoire
(define-type-alias Store (Listof Storage))
(define mt-store empty)
(define (override-store c l)
  (if (empty? l)
      (cons c empty)
      (let ([c2 (first l)])
        (if (equal? (cell-location c) (cell-location c2))
            (cons c (rest l))
            (cons (first l) (override-store c (rest l)))))))   
      

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))]) 
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    [(s-exp-match? `{box ANY} s)
     (let ([sl (s-exp->list s)])
       (boxE (parse (second sl))))]
    [(s-exp-match? `{unbox ANY} s)
     (let ([sl (s-exp->list s)])
       (unboxE (parse (second sl))))]
    [(s-exp-match? `{set-box! ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (setboxE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{begin ANY ANY ...} s)
     (let ([sl (s-exp->list s)])
       (beginE (parse (second sl)) (map parse (rest (rest sl)))))]
    [(s-exp-match? `{set! ANY SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (parse (second sl)) (s-exp->symbol (third sl)) (parse (fourth sl))))]
    

    [(s-exp-match? `{record [SYMBOL ANY] ...} s)
     (let ([sl (s-exp->list s)])
       (recordE (map (lambda (l) (s-exp->symbol (first (s-exp->list l)))) (rest sl))
                (map (lambda (l) (parse (second (s-exp->list l)))) (rest sl))))]
     [(s-exp-match? `{get ANY SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (getE (parse (second sl)) (s-exp->symbol (third sl))))]
    

    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env] [sto : Store]) : Result
  (type-case Exp e
    [(numE n) (v*s (numV n) sto)]
    [(idE s) (v*s (lookup s env) sto)]
    [(plusE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num+ v-l v-r) sto-r)))]
    [(multE l r)
     (with [(v-l sto-l) (interp l env sto)] 
           (with [(v-r sto-r) (interp r env sto-l)] 
                 (v*s (num* v-l v-r) sto-r)))] 
    
    
    [(lamE par body) (v*s (closV par body env) sto)]
    [(appE f arg)
     (with [(v-f sto-f) (interp f env sto)]
           (type-case Value v-f
             [(closV par body c-env)
              (with [(v-arg sto-arg) (interp arg env sto-f)]
                    (interp body (extend-env (bind par v-arg) c-env) sto-arg))]
             [else (error 'interp "not a function")]))]
    [(letE s rhs body)
     (with [(v-rhs sto-rhs) (interp rhs env sto)]
           (interp body (extend-env (bind s v-rhs) env) sto-rhs))] 
    [(boxE val)
     (with [(v-val sto-val) (interp val env sto)]
           (let ([l (new-loc sto-val)]) 
             (v*s (boxV l) (override-store (cell l v-val) sto))))]
    [(unboxE b)
     (with [(v-b sto-b) (interp b env sto)]
           (type-case Value v-b
             [(boxV l) (v*s (fetch l sto-b) sto-b)]
             [else (error 'interp "not a box")]))]
    [(setboxE b val)
     (with [(v-b sto-b) (interp b env sto)]
           (type-case Value v-b
             [(boxV l)
              (with [(v-val sto-val) (interp val env sto-b)]
                    (v*s v-val (override-store (cell l v-val) sto)))] 
             [else (error 'interp "not a box")]))]
    [(beginE l r) (beg l r env sto)]
    [(recordE s e) (let ([a (rec e empty env sto)]) (v*s (recV s (fst a)) (snd a)))] 

    
    [(getE e s)
     (let ([a (v*s-v (interp e env sto))]) 
     (type-case Value a 
       [(recV fds vs) (v*s (fetch (find s fds vs) sto) sto)]  
       [else (error 'interp "not a record")]))]

    [(setE e s e2)
     (let ([a (v*s-v (interp e env sto))])
     (type-case Value a
       [(recV fds vs) (let ([b (interp e2 env sto)]) (v*s (v*s-v b) (override-store (cell (find s fds vs) (v*s-v b)) (v*s-s b))))] 
       [else (error 'interp "not a record")]))] 
    ))     

; Fonctions utilitaires pour l'arithmétique 

(define (update [fd : Symbol] [new-val : Value]
                [fds : (Listof Symbol)] [vs : (Listof Value)] sto)
  (cond
    [(empty? fds) (error 'interp "no such field")]
    [(equal? fd (first fds)) (cons new-val (rest vs))]
    [else (cons (first vs) (update fd new-val (rest fds) (rest vs) sto))]))


(define (rec e l env sto)
  (if (empty? e)
      (pair l sto)
      (with [(v-l sto-l) (interp (first e) env sto)]
            (let ([loc (new-loc sto-l)]) 
                  (rec (rest e) (append l (list loc)) env (override-store (cell loc v-l) sto-l)))))      
  ) 

(define (find [fd : Symbol] [fds : (Listof Symbol)] [vs : (Listof Location)]) : Location
  (cond
    [(empty? fds) (error 'interp "no such field")] 
    [(equal? fd (first fds)) (first vs)]
    [else (find fd (rest fds) (rest vs))])) 

(define (beg l r env sto)
  (if (empty? r)
      (interp l env sto)
      (with [(v-l sto-l) (interp l env sto)] 
            (beg (first r) (rest r) env sto-l))))  
      
  

(define (num-op [op : (Number Number -> Number)] 
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-val (first env))] 
    [else (lookup n (rest env))]))

; Renvoie une adresse mémoire libre
(define (new-loc [sto : Store]) : Location
  (+ (max-address sto) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : Store]) : Location
  (if (empty? sto)
      0
      (max (cell-location (first sto)) (max-address (rest sto)))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(empty? sto) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first sto))) (cell-val (first sto))]
    [else (fetch l (rest sto))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;
 
(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))


( test ( interp ( parse `{ set-box! { box 2} 3}) mt-env mt-store )

       (v*s ( numV 3) ( list ( cell 1 ( numV 3)))))



(test (interp (parse `{let {[b { box 0}]}

                        {let {[c {box 1}]}

                          {let {[a {box 2}]}

                            {set-box! b 8}}}}) mt-env mt-store )

      (v*s (numV 8) (list (cell 1 (numV 8)) (cell 2 (numV 1)) (cell 3 (numV 2)))))



( test ( interp-expr `{ let {[b { box 0}]}

                         { begin

                            { set-box! b {+ 1 { unbox b} } }

                            { set-box! b {* 2 { unbox b} } }

                            { set-box! b {+ 3 { unbox b} } }

                            { set-box! b {+ 8 { unbox b} } }

                            { set-box! b {* 3 { unbox b} } }}})

       ( numV 39))



(test (interp-expr `{let {[b {box 0}]}

                      {begin

                        {set-box! b {+ 1 {unbox b}}}

                        }})

      (numV 1))



(test (interp-expr `{let {[r {record [x 1] [y 2]}]}

                      {get r x}}) (numV 1))



( test ( interp-expr `{ let {[a { box 1}]}

                         { let {[r { record

                                     [a { set-box! a {* 2 { unbox a} } }]

                                     [b { set-box! a {* 2 { unbox a} } }]}]}

                            {+ { unbox a} {+ { get r a} { get r b} } } } })

       ( numV 10))

(test (interp-expr `{let {[r {record [x 1] [y 2]}]}

                      {get r y}}) (numV 2))

(test (interp-expr `{let {[r {record [x 1] [y {+ 2 3}]}]}

                      {get r y}}) (numV 5))

(test (interp-expr `{let {[r {record [x 1]}]}

                      {get r x}}) (numV 1))

(test/exn (interp-expr `{{record [x 0]} 1}) "not a function")

(test/exn (interp-expr `{+ {record [x 0]} 1}) "not a number")

(test (interp-expr `{let {[b1 {box 1}]}

                      {let {[b2 {box 2}]}

                        {let {[v {set-box! b1 3}]}

                          {unbox b2}}}})

      (numV 2))



(test (interp-expr `{let {[b1 {box 1}]}

                      {let {[b2 {box 2}]}

                        {let {[v {set-box! b2 3}]}

                          {unbox b1}}}})

      (numV 1))

( test ( interp-expr `{ let {[r { record [a 1]}]}

                         { begin { set! r a 2} { get r a} } })

       ( numV 2))

( test ( interp-expr `{ let {[r { record [a 1] [b 2]}]}

                         { begin

                            { set! r a {+ { get r b} 3} }

                            { set! r b {* { get r a} 4} }

                            {+ { get r a} { get r b} } } })

       ( numV 25))

( interp-expr `{ let {[r { record [a 1] [b 2] [c 5]}]}
                  { begin
                     { set! r a {+ { get r b} 3} } 
                     { set! r c {* { get r c} 4} }
                     { set! r b {* { get r c} 4} }}})

(interp-expr `{ let {[r { record [a 1] [b 2] [c 5]}]}  
                  
                     { set! r b 3} })