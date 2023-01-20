#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "check.rkt")

(provide (all-defined-out))

(: maximal-value Integer)
(define maximal-value 9999)

(: minimal-value Integer)
(define minimal-value -9999)

(: find-optimal-element (All (A) (-> (Listof A) (-> A A Boolean) A A)))
(define (find-optimal-element l better best-so-far)
  (match l
    ['() best-so-far]
    [(cons a rest)
     (if (better a best-so-far)
         (find-optimal-element rest better a)
         (find-optimal-element rest better best-so-far))]))

(define-type Position-evaluation (U Normal-evaluation Checkmate-evaluation 'stalemate))
(struct Normal-evaluation ([value : Integer]) #:transparent)
(struct Checkmate-evaluation ([color : Color]) #:transparent)

(: position-evaluation<= (-> Position-evaluation Position-evaluation Boolean))
(define (position-evaluation<= ev1 ev2)
  (match* (ev1 ev2)
    [((Normal-evaluation v1) (Normal-evaluation v2)) (<= v1 v2)]
    [((Normal-evaluation v) (Checkmate-evaluation c))
     (if (equal? c 'white) #t #f)]
    [((Normal-evaluation v) 'stalemate) (<= v 0)]
    [((Checkmate-evaluation c) _) (if (equal? c 'black) #t #f)]
    [('stalemate (Normal-evaluation v)) (<= 0 v)]
    [('stalemate (Checkmate-evaluation c)) (if (equal? c 'white) #t #f)]
    [('stalemate 'stalemate) #t]))

(define-type Move-evaluation (U Normal-move-evaluation Checkmate-move-evaluation
                                No-move-evaluation))
(struct Normal-move-evaluation ([move : Move] [v : Integer]) #:transparent)
(struct Checkmate-move-evaluation ([move : Move]
                                   [in-moves : Integer]
                                   [color : Color]) #:transparent)
(struct No-move-evaluation ([v : Position-evaluation]) #:transparent)

(: move-evaluation<= (-> Move-evaluation Move-evaluation Boolean))
(define (move-evaluation<= ev1 ev2)
  (match* (ev1 ev2)
    [((Normal-move-evaluation _ v1) (Normal-move-evaluation _ v2))
     (<= v1 v2)]
    [((Normal-move-evaluation _ v) (Checkmate-move-evaluation _ in-moves c))
     (if (equal? c 'white) #t #f)]
    [((Normal-move-evaluation _ v) (No-move-evaluation pv))
     (position-evaluation<= (Normal-evaluation v) pv)]
    [((Checkmate-move-evaluation _ _ c) (Normal-move-evaluation _ v))
     (if (equal? c 'black) #t #f)]
    [((Checkmate-move-evaluation _ n1 c1) (Checkmate-move-evaluation _ n2 c2))
     (match* (c1 c2)
       [('white 'white) (<= n2 n1)]
       [('white 'black) #f]
       [('black 'white) #t]
       [('black 'black) (<= n1 n2)])]
    [((Checkmate-move-evaluation _ _ c) (No-move-evaluation v))
     (position-evaluation<= (Checkmate-evaluation c) v)]
    [((No-move-evaluation pv) (Normal-move-evaluation _ v))
     (position-evaluation<= pv (Normal-evaluation v))]
    [((No-move-evaluation v) (Checkmate-move-evaluation _ _ c))
     (position-evaluation<= v (Checkmate-evaluation c))]
    [((No-move-evaluation v1) (No-move-evaluation v2))
     (position-evaluation<= v1 v2)]))

(: move-evaluation> (-> Move-evaluation Move-evaluation Boolean))
(define (move-evaluation> ev1 ev2)
  (not (move-evaluation<= ev1 ev2)))

(: value-of-normal-evaluation (-> Move-evaluation Integer))
(define (value-of-normal-evaluation ev)
  (match ev
    [(Normal-move-evaluation _ v) v]
    [_ 0]))

(: discounted-evaluation (-> Move Move-evaluation Move-evaluation))
(define (discounted-evaluation move ev)
  (match ev
    [(Normal-move-evaluation _ v) (Normal-move-evaluation move v)]
    [(Checkmate-move-evaluation _ in-moves c)
     (Checkmate-move-evaluation move (+ in-moves 1) c)]
    [(No-move-evaluation pv)
     (match pv
       [(Normal-evaluation v) (Normal-move-evaluation move v)]
       [(Checkmate-evaluation c) (Checkmate-move-evaluation move 1 c)]
       ['stalemate (Normal-move-evaluation move 0)])]))

(: minimal-evaluation (-> (Listof Move-evaluation) Move-evaluation))
(define (minimal-evaluation l)
  (match l
    ['() (No-move-evaluation (Normal-evaluation maximal-value))]
    [(cons h tl) (find-optimal-element tl move-evaluation<= h)]))

(: maximal-evaluation (-> (Listof Move-evaluation) Move-evaluation))
(define (maximal-evaluation l)
  (match l
    ['() (No-move-evaluation (Normal-evaluation minimal-value))]
    [(cons h tl) (find-optimal-element tl move-evaluation> h)]))

(: evaluation-function-for-player
   (-> Color (-> (Listof Move-evaluation) Move-evaluation)))
(define (evaluation-function-for-player c)
  (match c
    ['white maximal-evaluation]
    ['black minimal-evaluation]))

(: evaluate-moves (-> (-> Position Position-evaluation)
                      (-> Position (Listof Move))
                      Integer Position (Listof Move-evaluation)))
(define (evaluate-moves evaluate-position determine-candidate-moves depth pos)
  (let ([moves-to-consider (determine-candidate-moves pos)])
    (if (empty? moves-to-consider)
        (list (No-move-evaluation (evaluate-position pos)))
        (cond
          [(= depth 0) (list (No-move-evaluation (evaluate-position pos)))]
          [(> depth 0)
           (let* ([player (Position-to-move pos)]
                  [opponent (opponent-of player)]
                  [min-or-max (evaluation-function-for-player opponent)]
                  [evaluate-move
                   (lambda ([move : Move])
                     (discounted-evaluation
                      move
                      (min-or-max
                       (evaluate-moves evaluate-position
                                       determine-candidate-moves
                                       (- depth 1)
                                       (make-move pos move)))))])
             (map evaluate-move moves-to-consider))]
          [else '()]))))
