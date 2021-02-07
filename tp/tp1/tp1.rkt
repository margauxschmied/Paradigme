#lang plait

(define (somme [L : (Listof Number)]) : Number
  (if (empty? L)
      0
      (+ (first L) (somme (rest L)))))
  
  
(define (Append [LG : (Listof 'a)]
                [LD : (Listof 'a)]) : (Listof 'a)
     (foldr cons LD LG))

(define (Map [f : ('a -> 'b)] [L : (Listof 'a)]) : (Listof 'b)
  (if (empty? L)
      empty
      (cons (f (first L)) (Map f (rest L)))))

(define (Foldr f acc L)
  (if (empty? L)
      acc
      (f (first L) (Foldr f acc (rest L)))))

(define (Foldl f acc L)
  (if (empty? L)
      acc
      (Foldl f (f (first L) acc) (rest L))))

(define-type (Couple 'a 'b)
  [couple (fst : 'a) (snd : 'b)])

(define-type (Option 'a)
[vide]
[element (value : 'a)])

(define (find [AL : (Listof (Couple 'key 'value))] [key : 'key]) : (Option 'value)
  (cond
    [(empty? AL) (vide)]
    [(equal? (couple-fst (first AL)) key) (element (couple-snd (first AL)))]
    [else (find (rest AL) key)]))



