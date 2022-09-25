#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")

(provide (all-defined-out))

(: make-from-to-move-pp! (-> Piece-placements Square-location Square-location
                            Piece-placements))
(define (make-from-to-move-pp! pp from to)
  (let ([from-square (get-square-by-location pp from)])
      (set-square-by-location! pp to from-square)
      (set-square-by-location! pp from 'empty-square)))

(: en-passant-step? (-> Square-location Square-location Color Boolean))
(define (en-passant-step? from to c)
  (let ([from-rank (Square-location-rank from)]
        [from-file (Square-location-file from)]
        [to-rank (Square-location-rank to)]
        [to-file (Square-location-file to)])
  (match c
    ['white (and (= from-rank 4) (= to-rank 5) (= (difference from-file to-file) 1))]
    ['black (and (= from-rank 3) (= to-rank 2) (= (difference from-file to-file) 1))])))

(: en-passant-capture-rank (-> Color Integer))
(define (en-passant-capture-rank c)
  (match c
    ['white 4]
    ['black 3]))



  