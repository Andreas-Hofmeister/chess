#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(provide (all-defined-out))

(: knight-moves (-> Square-location Color Position (Listof Move)))
(define (knight-moves from-loc c pos)
  (let* ([pp (Position-pp pos)]
         [from-rank (Square-location-rank from-loc)]
         [from-file (Square-location-file from-loc)]
         [all-to-locs
          (list (Square-location (+ from-rank 1) (+ from-file 2))
                (Square-location (+ from-rank 2) (+ from-file 1))
                (Square-location (+ from-rank 2) (- from-file 1))
                (Square-location (+ from-rank 1) (- from-file 2))
                (Square-location (- from-rank 1) (- from-file 2))
                (Square-location (- from-rank 2) (- from-file 1))
                (Square-location (- from-rank 2) (+ from-file 1))
                (Square-location (- from-rank 1) (+ from-file 2)))]
         [valid-to-locs
          (filter (lambda ([loc : Square-location])
                    (and (location-valid? loc)
                         (not (location-occupied-by-friendly-piece? pp loc c))))
                  all-to-locs)])
    (map (lambda ([loc : Square-location])
           (from-to-move-or-capture pp c from-loc loc))
         valid-to-locs)))
