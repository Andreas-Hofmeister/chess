#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")

(: king-moves (-> Square-location Color Position (Listof Move)))
(define (king-moves from-loc c pos)
  (let* ([pp (Position-pp pos)]
         [from-rank (Square-location-rank from-loc)]
         [from-file (Square-location-file from-loc)]
         [to-locs
          (filter (lambda ([loc : Square-location])
                    (not (location-occupied-by-friendly-piece? pp loc c)))
                  (adjacent-squares from-loc))])
     (map (lambda ([loc : Square-location])
           (from-to-move-or-capture pp c from-loc loc))
         to-locs)))
