#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "attacks.rkt")
(require "check.rkt")

(provide (all-defined-out))

(: puts-king-in-check? (-> Position Move Boolean))
(define (puts-king-in-check? pos move)
  (in-check? (