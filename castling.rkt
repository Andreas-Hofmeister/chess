#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "attacks.rkt")
(require "check.rkt")
(provide (all-defined-out))

(: empty-castling-squares (-> Color Castling-type (Listof Square-location)))
(define (empty-castling-squares c t)
  (match* (c t)
    [('white 'queen-side) (list (Square-location 0 1) (Square-location 0 2)
                                (Square-location 0 3))]
    [('white 'king-side) (list (Square-location 0 5) (Square-location 0 6))]
    [('black 'queen-side) (list (Square-location 7 1) (Square-location 7 2)
                                (Square-location 7 3))]
    [('black 'king-side) (list (Square-location 7 5) (Square-location 7 6))]))

(: rook-castling-square (-> Color Castling-type Square-location))
(define (rook-castling-square c t)
  (match* (c t)
    [('white 'queen-side) (Square-location 0 0)]
    [('white 'king-side) (Square-location 0 7)]
    [('black 'queen-side) (Square-location 7 0)]
    [('black 'king-side) (Square-location 7 7)]))

(: king-castling-square (-> Color Square-location))
(define (king-castling-square c)
  (match c
    ['white (Square-location 0 4)]
    ['black (Square-location 7 4)]))

(: can-make-castling-move (-> Position Color Castling-type Boolean))
(define (can-make-castling-move pos c ct)
  (let ([castling-availabilities (Position-castling-availabilities pos)]
        [pp (Position-pp pos)]
        [empty-squares (empty-castling-squares c ct)])
    (and (set-member? castling-availabilities (Castling-availability ct c))
         (equal? (get-square-by-location pp (rook-castling-square c ct))
                 (Occupied-square c 'rook))
         (equal? (get-square-by-location pp (king-castling-square c))
                 (Occupied-square c 'king))
         (forall-in empty-squares (curry square-empty? pp))
         (not (in-check? pos c))
         (forall-in empty-squares
                    (lambda ([loc : Square-location])
                      (not (attacks-empty-square? pos (opponent-of c) loc)))))))

(: castling-moves (-> Position Color (Listof Move)))
(define (castling-moves pos c)
  (append (if (can-make-castling-move pos c 'king-side)
              (list (Castle c 'king-side)) '())
          (if (can-make-castling-move pos c 'queen-side)
              (list (Castle c 'queen-side)) '())))
