; Cours 06 : Interpréteur pour le lambda-calcul à compléter

#lang plait

;;;;;;;;;;;;;;;
; Expressions ;
;;;;;;;;;;;;;;;

; Langage intermédiaire
(define-type ExpS
  [idS (s : Symbol)]
  [lamS (pars : (Listof Symbol)) (body : ExpS)]
  [appS (fun : ExpS) (args : (Listof ExpS))]
  [letS (pars : (Listof Symbol)) (args : (Listof ExpS)) (body : ExpS)]

  [numS (n : Number)]
  [add1S]
  [plusS]
  [multS] 

  [trueS]
  [falseS]
  [ifS (cnd : ExpS) (l : ExpS) (r : ExpS)]  
  [zeroS]

  [pairS] 
  [fstS]
  [sndS]
  [sub1S]
  [minusS] 
  
  [divS]
 
  [letrecS (par : Symbol) (arg : ExpS) (body : ExpS)])

; Le langage du lambda-calcul
(define-type Exp
  [idE (s : Symbol)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)])

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (compose f g)
  (lambda (x) (f (g x))))

(define (parse [s : S-Exp]) : ExpS
  (cond
    [(s-exp-match? `NUMBER s) (numS (s-exp->number s))]

    ; ensembles de symboles prédéfinis
    [(s-exp-match? `add1 s) (add1S)]
    [(s-exp-match? `+ s) (plusS)]
    [(s-exp-match? `sub1 s) (sub1S)]
    [(s-exp-match? `- s) (minusS)]
    [(s-exp-match? `* s) (multS)]
    [(s-exp-match? `/ s) (divS)]
    [(s-exp-match? `true s) (trueS)]
    [(s-exp-match? `false s) (falseS)]
    [(s-exp-match? `zero? s) (zeroS)]
    [(s-exp-match? `pair s) (pairS)]
    [(s-exp-match? `fst s) (fstS)]
    [(s-exp-match? `snd s) (sndS)]
    
    [(s-exp-match? `SYMBOL s) (idS (s-exp->symbol s))]
    [(s-exp-match? `{lambda {SYMBOL SYMBOL ...} ANY} s)
     (let ([sl (s-exp->list s)]) 
       (lamS (map s-exp->symbol (s-exp->list (second sl))) (parse (third sl))))]
    [(s-exp-match? `{let {[SYMBOL ANY] [SYMBOL ANY] ...} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([substs (map s-exp->list (s-exp->list (second sl)))])
         (letS (map (compose s-exp->symbol first) substs)
               (map (compose parse second) substs)
               (parse (third sl)))))]
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    [(s-exp-match? `{letrec {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([substs (s-exp->list (first (s-exp->list (second sl))))])
         (letrecS (s-exp->symbol (first substs))
                  (parse (second substs))
                  (parse (third sl)))))]  
    [(s-exp-match? `{ANY ANY ANY ...} s)
     (let ([sl (s-exp->list s)])
       (appS (parse (first sl)) (map parse (rest sl))))] 
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Retrait du sucre syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (desugar [e : ExpS]) : Exp 
  (type-case ExpS e
    [(idS s) (idE s)]
    [(lamS pars body) (if (>= (length pars) 1)
                          (lam pars body)
                          
                          (error 'desugar "not implemented"))]
    [(appS fun args) (if (>= (length args) 1)
                         (app (desugar fun) args)
                         (error 'desugar "not implemented"))]
    [(letS pars args body) (if (>= (length args) 1)
                               (app (lam pars body) args) 
                               (error 'desugar "not implemented"))] 
    [(numS n) (lamE 'f (lamE 'x (num n)))]
    [(add1S) (add1)]
    [(plusS) (add)]  
    [(multS) (mult)]
    [(trueS) (lamE 'x (lamE 'y (idE 'x)))]  
    [(falseS) (lamE 'x (lamE 'y (idE 'y)))] 
    [(ifS cnd l r) (iff (desugar cnd) (desugar l) (desugar r))]
    [(zeroS) (zero)]
    [(pairS) (pair)] 
    [(fstS) (fst)]
    [(sndS) (snd)]
    [(sub1S) (sub1)]
    [(minusS) (sub)]
    [(divS) (div)]
    [(letrecS par arg body) (letre par arg body)]  ))
;[else (begin (display e)(error 'desugar "not implemented"))])) 

;(λdiv.div (λf.λx.f (f (f (f x)))) (λf.λx.f (f x)))(λm.λn.(λdivinter.divinter m n n)((λbody-proc.(λfX.fX fX)(λfX.(λf.body-proc f)(λx.fX fX x)))(λdivinter.λm.λn.λk.(λn.n (λ_.λx.λy.y) (λx.λy.x)) k (λd.(λn.λm.m (λn.λf.λx.f (n f x)) n)(λf.λx.f x) (divinter m n n)) (λd.(λn.n (λ_.λx.λy.y) (λx.λy.x)) m (λd.λf.λx.x) (λd.divinter ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) m (λf.λx.f x)) n ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) k (λf.λx.f x))) _) _)))

;(define (div)
;  (let ([par (idE 'divinter)])
;    (let ([body (list par (idE'm) (idE'n) (idE'n))]) 
;      (let ([arg (lam (list (idE'm) (idE'n) (idE'k))
;                      (if ((zero) (idE'k))
;                          ((add1) (par (idE'm) (idE'n) (idE'n))) 
;                          (if ((zero) (idE 'm))
;                              (desugar (numS 0)) 
;                              (par (sub1) (idE 'm) (idE'n) (sub1) (idE 'k))))
;                          )])
;        (display arg))))
  
;  )

(define (div)
  (desugar
   (letS
    (list 'div 'm 'n) 
    (list
     (lamS
      '(m)
      (lamS 
       '(n)
       (letrecS
        'divinter
        (lamS
         '(m)
         (lamS
          '(n)
          (lamS
           '(k)
           (ifS
            (appS (zeroS) (list (idS 'k)))
            (appS (plusS) (list (numS 1) (appS (idS 'divinter) (list (idS 'm) (idS 'n) (idS 'n)))))
            (ifS (appS (zeroS) (list (idS 'm))) (numS 0) (appS (idS 'divinter) (list (appS (minusS) (list (idS 'm) (numS 1))) (idS 'n) (appS (minusS) (list (idS 'k) (numS 1))))))))))
        (appS (idS 'divinter) (list (idS 'm) (idS 'n) (idS 'n)))))))
    (appS (idS 'div) (list (idS'm) (idS'n))))))

  

(define (letre par arg body)
  
  ;(λbody-proc.(λfX.fX fX)(λfX.(λf.body-proc f)(λx.fX fX x)))  
  ;[(letrecS par arg body)
  (appE(lamE par
             (desugar body))
       (appE (body-proc)  
             (lamE par (desugar arg)))))  
 
(define (body-proc) 
  (lamE 'body-proc 
        (appE (lamE 'fX  
                    (appE (idE'fX)
                          (idE'fX)))
              (lamE 'fX
                    (appE (lamE 'f
                                (appE (idE'body-proc)  
                                      (idE'f)))
                          (lamE 'x (app (idE'fX) (list (idS'fX) (idS'x)))))))));(app (lamE 'x (idE'fX)) (list (idS'fX) (idS'x))))))))
 
;on veux:
;(λfac.fac (λf.λx.f (f (f (f (f (f x)))))))((λbody-proc.(λfX.fX fX)(λfX.(λf.body-proc f)(λx.fX fX x)))(λfac.λn.(λn.n (λ_.λx.λy.y) (λx.λy.x)) n (λ_.λf.λx.f x) (λ_.(λn.λm.n ((λn.λm.n (add1) m) m) (λf.λx.x)) n (fac ((λn.λm.m ((λshift.λn.(fst)(n shift ((pair)(λf.λx.x) (λf.λx.x))))(shift))) n) n (λf.λx.f x)))) _))

;on a:
;(λfac.fac (λf.λx.f (f (f (f (f (f x)))))))((λbody-proc.(λfX.fX fX)(λfX.(λf.body-proc f)((λx.fX) fX x)))(λfac.λn.(λn.n (λx.λx.λy.y) (λx.λy.x)) n (λd.λf.λx.f x) (λd.(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x)) n) n) (λf.λx.x)) n (fac ((λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n) n (λf.λx.f x)))) _))


                                         

(define (sub)
  ;sub ≡ λn.λm.m sub1 n
  ;λn.λm.m (λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))) n
  (lamavecE (list 'n 'm) (appE (appE (idE'm) (sub1)) (idE'n))))

(define (sub1)
  ;sub1 ≡ λn.fst (n shift (pair 0 0))
  ;λn.(λp.p (λx.λy.x))(n (λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))) ((λx.λy.λsel.sel x y)(λf.λx.x) (λf.λx.x)))
  (lamE 'n (appE (desugar (fstS)) (appE (appE (idE'n) (shift)) (appE (appE (desugar (pairS)) (desugar (numS 0))) (desugar (numS 0)))))))

(define (shift)
  ;shift ≡ λp.pair (snd p) (add1 (snd p))
  ;λp.(λx.λy.λsel.sel x y)((λp.p (λx.λy.y)) p) ((λn.λf.λx.f (n f x))((λp.p (λx.λy.y)) p))
  (lamE 'p (appE (appE (desugar (pairS)) (appE (desugar (sndS)) (idE 'p))) (appE (add1) (appE (desugar (sndS)) (idE 'p))))))


(define (snd)
  ;snd ≡ {lambda {p} {p false}}
  (lamE 'p (appE (idE 'p) (desugar (falseS))))
  )

(define (fst)
  ;fst ≡ {lambda {p} {p true}}
  (lamE 'p (appE (idE 'p) (desugar (trueS))))
  )
  
(define (pair)
  ;pair ≡ {lambda {x} {lambda {y} {lambda {sel} {{sel x} y}}}}
  (lamE 'x (lamE 'y (lamE 'sel (appE (appE (idE 'sel) (idE 'x)) (idE 'y)))))) 
  

(define (zero)
  ;λn.n (λx.false) true 
  (lamE 'n (appE (appE (idE 'n) (lamE '_ (desugar (falseS)))) (desugar (trueS)))))

(define (iff cnd l r)
  ;{{{test
  ;{lambda {d} if-true}}
  ;{lambda {d} if-false}} 0} 
  (appE (appE (appE cnd (lamE 'd l)) (lamE 'd r)) (idE '_)))

;{lambda {x} {lambda {y} x}} ≡ true
;{lambda {x} {lambda {y} y}} ≡ false 

(define (mult)
  ;λn.λm.m (add n) _
  ;(λn.λm.m ((λn.λm.m (λn.λf.λx.f (n f x)) n) n) _)(λf.λx.f (f (f (f (f (f (f (f (f (f x)))))))))) (λf.λx.f (f (f (f x))))
  (lamavecE (list 'n 'm) (appE (appE (idE'm) (appE (add) (idE 'n))) (desugar (numS 0))))) 

(define (add)
  ;λn.λm.m add1 n
  (lamavecE (list 'n 'm) (appE (appE (idE'm) (add1)) (idE 'n))))  

(define (add1)
  ;λn.λf.λx.f (n f x)
  ;(app (lam (list 'n 'f 'x) (idS 'f)) (list (idS 'n) (idS 'f) (idS 'x))))
  ;(lam (list 'n 'f 'x) (idE 'f))
  (lam (list 'n 'f 'x) (appS (idS'f) (list (appS (idS'n) (list (idS 'f) (idS 'x)))))))

(define (num n)
  (if (equal? n 0)
      (idE 'x)
      (appE (idE 'f) (num (- n 1)))))   

(define (app fun args)
  (if (empty? args)  
      fun
      (app (appE fun (desugar (first args))) (rest args))))



(define (lam pars body)
  (if (=(length pars) 1)
      (lamE (first pars) (desugar body)) 
      (lamE (first pars) (lam (rest pars) body))))

(define (lamavecE pars body)
  (if (=(length pars) 1)
      (lamE (first pars) body) 
      (lamE (first pars) (lamavecE (rest pars) body)))) 

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Substitution
(define (subst [what : Exp] [for : Symbol] [in : Exp]) : Exp
  (type-case Exp in 
    [(idE s) (if (equal? s for) what in)]
    [(lamE par body) (if (equal? par for) in (lamE par (subst what for body)))]
    [(appE fun arg) (appE (subst what for fun) (subst what for arg))]))
 
; Interpréteur (pas de décente dans un lambda) 
(define (interp [e : Exp]) : Exp 
  (type-case Exp e
    [(appE fun arg)
     (type-case Exp (interp fun) 
       [(lamE par body) (interp (subst (interp arg) par body))]
       [else e])] 
    [else e]))

; Concaténation de chaînes de caractères contenues dans une liste 
(define (strings-append [strings : (Listof String)]) : String
  (foldr string-append "" strings))

; Affichage lisible d'une lambda-expression 
(define (expr->string [e : Exp]) : String 
  (type-case Exp e
    [(idE s) (symbol->string s)]
    [(lamE par body) (strings-append (list "λ" (symbol->string par) "." (expr->string body)))]  
    [(appE fun arg)
     (let ([fun-string (if (lamE? fun)
                           (strings-append (list "(" (expr->string fun) ")"))
                           (expr->string fun))]
           [arg-string (if (idE? arg)
                           (expr->string arg)
                           (strings-append (list "(" (expr->string arg) ")")))])
       (if (and (lamE? fun) (not (idE? arg)))
           (string-append fun-string arg-string) 
           (strings-append (list fun-string " " arg-string))))]))

; Transforme une expression en nombre si possible
(define (expr->number [e : Exp]) : Number
  (type-case Exp (interp e)
    [(lamE f body-f)
     (type-case Exp (interp body-f)
       [(lamE x body-x)
        (destruct body-x f x)]
       [else (error 'expr->number "not a number")])]
    [else (error 'expr->number "not a number")])) 
          
; Compte le nombre d'application de f à x
(define (destruct [e : Exp] [f : Symbol] [x : Symbol]) : Number 
  (type-case Exp (interp e)
    [(idE s) (if (equal? s x)
                 0
                 (error 'expr->number "not a number"))] 
    [(lamE par body) (error 'expr->number "not a number")] 
    [(appE fun arg) (if (equal? fun (idE f))
                        (+ 1 (destruct arg f x))
                        (error 'expr->number "not a number"))]))

; Transforme une expression en booléen si possible
(define (expr->boolean [e : Exp]) : Boolean
  (type-case Exp (interp e)
    [(lamE x body-x)
     (type-case Exp (interp body-x)
       [(lamE y body-y)
        (type-case Exp (interp body-y)
          [(idE s) (cond
                     ((equal? x s) #t)
                     ((equal? y s) #f)
                     (else (error 'expr->boolean "not a boolean")))] 
          [else (error 'expr->boolean "not a boolean")])]
       [else (error 'expr->boolean "not a boolean")])]
    [else (error 'expr->boolean "not a boolean")]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-number expr)
  (expr->number (desugar (parse expr))))

(define (interp-boolean expr)
  (expr->boolean (desugar (parse expr))))

(test
 (expr->string (desugar (parse `{{lambda {x y z} body} a b c})))
 "(λx.λy.λz.body) a b c")

(test
 (expr->string (desugar (parse `{let {[x a] [y b] [z c]} body}))) 
 "(λx.λy.λz.body) a b c") 


(test (interp-number `0) 0) 
(test (interp-number `10) 10) 
(test (interp-number `{add1 4}) 5)   
(test (interp-number `{+ 4 2}) 6) 
(test (interp-number `{* 10 4}) 40)

(test (interp-boolean `true) #t)
(test (interp-boolean `false) #f)
(test (interp-number `{if true 0 1}) 0)
(test (interp-number `{if false 0 1}) 1)
(test ( interp-number `{if true 5 1}) 5)
(test ( interp-number `{if false 5 1}) 1)
(test (interp-boolean `{zero? 0}) #t) 
(test (interp-boolean `{zero? 1}) #f)

(test (interp (desugar (parse `{fst {pair a b}}))) (idE 'a))
(test (interp (desugar (parse `{snd {pair a b}}))) (idE 'b)) 
(test (interp-number `{sub1 4}) 3) 
(test (interp-number `{- 4 3}) 1)
(test (interp-number `{- 1 2}) 0)  

(test (interp-number`{letrec {[fac {lambda {n}{if {zero? n} 1{* n {fac {- n 1}}}}}]}{fac 6}}) 720)
;(test (interp-number`{letrec {[fac {lambda {n} {lambda {a}
;                                                 {if {zero? n}
;                                                     a
;                                                     (fac (- n 1)(+ a 1)) }}}]}  
;                       {fac 10 3}}) 13)   
 

;(expr->string (desugar (parse `{let {[div {lambda {m} {lambda {n} 
;                                                        {letrec {[divinter {lambda {m} {lambda {n} {lambda {k}
;                                                                                        
;                                                                                                     {if {zero? k}
;                                                                                                         (+ 1 (divinter m n n))
;                                                                                                         {if {zero? m}
;                                                                                                             0
;                                                                                                             (divinter (- m 1) n (- k 1))}}}}}]}
;                                                          {divinter m n n}}}}]}
;
;                                                 
;                                 {div 4 2}}) )) 


(test (interp-number `{/ (+ 8 0) 4}) 2)   



