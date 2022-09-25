#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "pawn-moves.rkt")
(require "rook-moves.rkt")
(require "knight-moves.rkt")
(require "bishop-moves.rkt")
(require "queen-moves.rkt")
(require "king-moves.rkt")

(provide (all-defined-out))

(: moves-by-player-from-square (-> Position Color Square-location (Listof Move)))
(define (moves-by-player-from-square pos c loc)
  (let ([pp (Position-pp pos)]
        [from-rank (Square-location-rank loc)]
        [from-file (Square-location-file loc)])
    (match (get-square pp from-rank from-file)
      ['empty-square '()]
      [(Occupied-square square-color piece)
       (if (equal? square-color c)
           (match piece
             ['pawn (pawn-moves loc c pos)]
             ['rook (rook-moves loc c pos)]
             ['bishop (bishop-moves loc c pos)]
             ['knight (knight-moves loc c pos)]
             ['queen (queen-moves loc c pos)]
             ['king (king-moves loc c pos)])
           '())])))

(: moves-by-player (-> Position Color (Listof Move)))
(define (moves-by-player pos c)
  (append* (map (lambda ([loc : Square-location])
                  (moves-by-player-from-square pos c loc))
                valid-locations)))

(: move-that-attacks-empty-square? (-> Square-location Move Boolean))
(define (move-that-attacks-empty-square? loc move)
  (and (move-to-empty-square? move) (equal? (to-of-move move) loc)))

(: attacks-empty-square? (-> Position Color Square-location Boolean))
(define (attacks-empty-square? pos c loc)
  (exists-in (moves-by-player pos c)
             (curry move-that-attacks-empty-square? loc)))

(: move-that-attacks-occupied-square? (-> Square-location Move Boolean))
(define (move-that-attacks-occupied-square? loc move)
  (and (capturing-move? move) (equal? (to-of-move move) loc)))

(: attacks-occupied-square? (-> Position Color Square-location Boolean))
(define (attacks-occupied-square? pos c loc)
  (exists-in (moves-by-player pos c)
             (curry move-that-attacks-occupied-square? loc)))

(: attacks-square? (-> Position Color Square-location Boolean))
(define (attacks-square? pos c loc)
  (or (attacks-empty-square? pos c loc) (attacks-occupied-square? pos c loc)))

