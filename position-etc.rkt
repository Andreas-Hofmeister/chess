#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "fen.rkt")

(provide (all-defined-out))

; A position together with useful information about it
(struct Position-etc ([position : Position]
                      [legal-moves : (Listof Move)]
                      [white-king-location : Square-location]
                      [white-queens : (Setof Square-location)]
                      [white-rooks : (Setof Square-location)]
                      [white-knights : (Setof Square-location)]
                      [white-bishops : (Setof Square-location)]
                      [white-pawns : (Setof Square-location)]
                      [black-king-location : Square-location]
                      [black-queens : (Setof Square-location)]
                      [black-rooks : (Setof Square-location)]
                      [black-knights : (Setof Square-location)]
                      [black-bishops : (Setof Square-location)]
                      [black-pawns : (Setof Square-location)])
  #:transparent)

(: position-etc-from-position (-> Position Position-etc))
(define (position-etc-from-position pos)
  (let* ([pp (Position-pp pos)]
         [moves (legal-moves pos)]
         [white-king-location (Square-location 0 0)]
         [white-queens : (Setof Square-location) (set)]
         [white-rooks : (Setof Square-location) (set)]
         [white-knights : (Setof Square-location) (set)]
         [white-bishops : (Setof Square-location) (set)]
         [white-pawns : (Setof Square-location) (set)]
         [black-king-location (Square-location 0 0)]
         [black-queens : (Setof Square-location) (set)]
         [black-rooks : (Setof Square-location) (set)]
         [black-knights : (Setof Square-location) (set)]
         [black-bishops : (Setof Square-location) (set)]
         [black-pawns : (Setof Square-location) (set)])
    (for ([loc valid-locations])
      (match (get-square-by-location pp loc)
        [(Occupied-square 'white 'king) (set! white-king-location loc)]
        [(Occupied-square 'white 'queen) (set! white-queens (set-add white-queens loc))]
        [(Occupied-square 'white 'rook) (set! white-rooks (set-add white-rooks loc))]
        [(Occupied-square 'white 'knight) (set! white-knights (set-add white-knights loc))]
        [(Occupied-square 'white 'bishop) (set! white-bishops (set-add white-bishops loc))]
        [(Occupied-square 'white 'pawn) (set! white-pawns (set-add white-pawns loc))]
        [(Occupied-square 'black 'king) (set! black-king-location loc)]
        [(Occupied-square 'black 'queen) (set! black-queens (set-add black-queens loc))]
        [(Occupied-square 'black 'rook) (set! black-rooks (set-add black-rooks loc))]
        [(Occupied-square 'black 'knight) (set! black-knights (set-add black-knights loc))]
        [(Occupied-square 'black 'bishop) (set! black-bishops (set-add black-bishops loc))]
        [(Occupied-square 'black 'pawn) (set! black-pawns (set-add black-pawns loc))]
        [_ 'do-nothing]))
    (Position-etc pos
                  moves
                  white-king-location
                  white-queens
                  white-rooks
                  white-knights
                  white-bishops
                  white-pawns
                  black-king-location
                  black-queens
                  black-rooks
                  black-knights
                  black-bishops
                  black-pawns)))

;(define pos1 (pos-from-fen "1r4k1/1r3ppn/4p3/4P1pP/2pP2P1/3Q1P2/P3R3/K1BBq3 w - - 0 1"))
;(define etc1 (position-etc-from-position pos1))
