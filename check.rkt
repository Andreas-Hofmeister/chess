#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "attacks.rkt")

(provide (all-defined-out))

(: find-king (-> Position Color (Listof Square-location)))
(define (find-king pos c)
  (find-piece pos c 'king valid-locations))

(: in-check? (-> Position Color Boolean))
(define (in-check? pos c)
  (exists-in (find-king pos c)
             (lambda ([king-loc : Square-location])
               (attacks-occupied-square? pos (opponent-of c) king-loc))))
