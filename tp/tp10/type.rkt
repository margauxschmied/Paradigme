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
  [sndE (e : Exp)])

; Représentation du type des expressions
(define-type Type
  [numT]
  [boolT]
  [prodT (f : Type) (s : Type)]
  [arrowT (par : Type) (res : Type)])

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
  [closV (par : Symbol) (body : Exp) (env : Env)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])

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
    [(s-exp-match? `(ANY -> ANY) s)
     (let ([sl (s-exp->list s)])
       (arrowT (parse-type (first sl))
               (parse-type (third sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Vérification des types ;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (typecheck [e : Exp] [env : TypeEnv]) : Type
  (type-case Exp e
    [(numE n) (numT)]
    [(idE s) (type-lookup s env)]
    [(plusE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(multE l r)
     (let ([t1 (typecheck l env)]
           [t2 (typecheck r env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (numT)]
            [else (type-error r (numT) t2)])]
         [else (type-error l (numT) t1)]))]
    [(lamE par par-type body)
     (arrowT par-type
             (typecheck body
                        (extend-env (tbind par par-type) env)))]
    [(appE fun arg)
     (let ([t1 (typecheck fun env)]
           [t2 (typecheck arg env)])
       (type-case Type t1
         [(arrowT par-type res-type)
          (if (equal? par-type t2)
              res-type
              (type-error arg par-type t2))]
         [else (type-error-function fun t1)]))]
    [(boolE b) (boolT)]
    [(equE e1 e2)
     (let ([t1 (typecheck e1 env)]
           [t2 (typecheck e2 env)])
       (type-case Type t1
         [(numT)
          (type-case Type t2
            [(numT) (boolT)] 
            [else (type-error e2 (numT) t2)])]
         [else (type-error e1 (numT) t1)]))]
    [(ifE cnd e1 e2) 
     (let ([c (typecheck cnd env)]
           [t1 (typecheck e1 env)]
           [t2 (typecheck e2 env)])  
       (type-case Type c
         [(boolT) 
          (if (equal? t1 t2)
              t1 
              (type-error e2 t1 t2))] 
         [else (type-error cnd (boolT) c)]))]
    [(pairE f s) (prodT (typecheck f env) (typecheck s env))]
    [(fstE e)
     (let ([p (typecheck e env)])  
       (type-case Type p
         [(prodT f s) f] 
         [else (type-error e (prodT none none) p)]))]
    [(sndE e)
     (let ([p (typecheck e env)])  
       (type-case Type p
         [(prodT f s) s] 
         [else (type-error e (prodT) p)]))]
    ))
    

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
        (interp body (extend-env (bind par (interp arg env)) c-env))]
       [else (error 'interp "not a function")])]
    [(boolE b) (boolV b)]
    [(equE l r) (num= (interp l env) (interp r env))]                      
    [(ifE q f s) (num-if q f s env)]
    [(pairE f s) (pairV (interp f env) (interp s env))]
    [(fstE e) (type-case Value (interp e env)
                [(pairV f s) f] 
                [else (error 'interp "not a pair")])]  
    [(sndE e) (type-case Value (interp e env)
                [(pairV f s) s]
                [else (error 'interp "not a pair")])]))

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
(define (lookup [s : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? s (bind-name (first env))) (bind-val (first env))]
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

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value 
  (let ([expr (parse e)])
    (begin
      (typecheck expr mt-env)
      (interp expr mt-env))))

(define (typecheck-expr [e : S-Exp]) : Type
  (typecheck (parse e) mt-env)) 

(test (typecheck-expr `{= 1 2}) (boolT))
(test (typecheck-expr `{if {= 1 2} true false}) (boolT))
(test/exn (typecheck-expr `{if 1 2 3}) "typecheck")

(test (typecheck-expr `{pair 1 true}) (prodT (numT) (boolT))) (test (typecheck-expr `{fst {pair 1 true}}) (numT))
(test (typecheck-expr `{snd {pair 1 true}}) (boolT))
(test (typecheck-expr `{lambda {[x : (num * bool)]} {fst x}})
(arrowT (prodT (numT) (boolT)) (numT)))