#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "attacks.rkt")

(provide (all-defined-out))

(: in-check? (-> Position Color Boolean))
(define (in-check? pos c)
  (exists-in (find-king (Position-pp pos) c)
             (lambda ([king-loc : Square-location])
               (attacks-occupied-square? pos (opponent-of c) king-loc))))

