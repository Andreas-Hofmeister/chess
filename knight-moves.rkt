#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(provide (all-defined-out))

(: knight-target-squares (-> Square-location (Listof Square-location)))
(define (knight-target-squares from-loc)
  (let ([from-rank (Square-location-rank from-loc)]
        [from-file (Square-location-file from-loc)])
    (filter location-valid?
            (list (Square-location (+ from-rank 1) (+ from-file 2))
                  (Square-location (+ from-rank 2) (+ from-file 1))
                  (Square-location (+ from-rank 2) (- from-file 1))
                  (Square-location (+ from-rank 1) (- from-file 2))
                  (Square-location (- from-rank 1) (- from-file 2))
                  (Square-location (- from-rank 2) (- from-file 1))
                  (Square-location (- from-rank 2) (+ from-file 1))
                  (Square-location (- from-rank 1) (+ from-file 2))))))

(: knight-moves (-> Square-location Color Position (Listof Move)))
(define (knight-moves from-loc c pos)
  (let* ([pp (Position-pp pos)]
         [from-rank (Square-location-rank from-loc)]
         [from-file (Square-location-file from-loc)]
         [all-valid-to-locs (knight-target-squares from-loc)]
         [viable-to-locs
          (filter (lambda ([loc : Square-location])
                    (not (location-occupied-by-friendly-piece? pp loc c)))
                  all-valid-to-locs)])
    (map (lambda ([loc : Square-location])
           (from-to-move-or-capture pp c from-loc loc))
         viable-to-locs)))
