; Cours 02 : Expressions arithmétiques

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions dans le langage utilisateur
(define-type Exp
  [numE (n : Number)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)])

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp]) : Number
  (type-case Exp e
    [(numE n) n]
    [(plusE l r) (+ (interp l) (interp r))]
    [(multE l r) (* (interp l) (interp r))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(test (interp (numE 1)) 1)
(test (interp (plusE (numE 1) (numE 2))) 3)
(test (interp (multE (numE 2) (numE 3))) 6)
(test (interp (plusE (numE 1) (multE (numE 2) (numE 3)))) 7)