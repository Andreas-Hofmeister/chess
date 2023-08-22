#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
;(require "make-move.rkt")
(require "check.rkt")
(require "attacks-defenses-v1.rkt")
(require "move-search.rkt")

(provide (all-defined-out))

(struct Position-info ([pos : Position]
                       [equivalent-trades : (Option (Listof Square-location))]
                       [en-prise : (Option (Listof Square-location))]
                       [enemies-en-prise : (Option (Listof Square-location))]
                       [own-en-prise : (Option (Listof Square-location))]
                       [defenses : (Option Defenses)]
                       [sorted-white-defenses : (Option (HashTable Square-location (Listof Defense)))]
                       [sorted-black-defenses : (Option (HashTable Square-location (Listof Defense)))]
                       [attacks : (Option Attacks)]
                       [sorted-white-attacks : (Option (HashTable Square-location (Listof Attack)))]
                       [sorted-black-attacks : (Option (HashTable Square-location (Listof Attack)))]
                       [defenses-by-target : (Option (HashTable Square-location (Listof Defense)))]
                       [in-check? : (Option Boolean)]
                       [legal-moves : (Option (Listof Move))]
                       [checkmate-threats : (Option (Listof Move))])
  #:transparent
  #:mutable)

(: make-empty-pos-info (-> Position Position-info))
(define (make-empty-pos-info pos)
  (Position-info pos 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none))

(: Pos-info-pp (-> Position-info Piece-placements))
(define (Pos-info-pp pos-info)
  (Position-pp (Position-info-pos pos-info)))

(: make-Pos-info-getter (All (A) (-> (-> Position-info (Option A))
                                     (-> Position-info (Option A) Void)
                                     (-> Position-info A)
                                     (-> Position-info A))))
(define (make-Pos-info-getter getter setter! calculator)
  (lambda ([pos-info : Position-info])
    (match (getter pos-info)
      ['none
       (let ([calculated (calculator pos-info)])
         (setter! pos-info (Some calculated))
         calculated)]
      [(Some already-calculated) already-calculated])))

(: Pos-info-checkmate-threats (-> Position-info (Listof Move)))
(define Pos-info-checkmate-threats
  (make-Pos-info-getter Position-info-checkmate-threats
                        set-Position-info-checkmate-threats!
                        (lambda ([pos-info : Position-info])
                          (let* ([rev-pos (switch-to-move (Position-info-pos pos-info))]
                                 [rev-moves (legal-moves rev-pos)])
                            (moves-of-evaluations (forced-mate-moves (forced-mate-search 1 rev-pos)))))))

(: Pos-info-legal-moves (-> Position-info (Listof Move)))
(define Pos-info-legal-moves
  (make-Pos-info-getter Position-info-legal-moves
                        set-Position-info-legal-moves!
                        (lambda ([pos-info : Position-info])
                          (legal-moves (Position-info-pos pos-info)))))

(: Pos-info-in-check? (-> Position-info Boolean))
(define Pos-info-in-check?
  (make-Pos-info-getter Position-info-in-check?
                        set-Position-info-in-check?!
                        (lambda ([pos-info : Position-info])
                          (in-check? (Position-info-pos pos-info)
                                     (Position-to-move (Position-info-pos pos-info))))))

(: Pos-info-attacks (-> Position-info Attacks))
(define Pos-info-attacks
  (make-Pos-info-getter Position-info-attacks
                        set-Position-info-attacks!
                        (lambda ([pos-info : Position-info])
                          (attacks-of-pp (Pos-info-pp pos-info)))))

(: Pos-info-own-attacks (-> Position-info (Listof Attack)))
(define (Pos-info-own-attacks pos-info)
  (if (eq? (Position-to-move (Position-info-pos pos-info)) 'white)
      (Attacks-white (Pos-info-attacks pos-info))
      (Attacks-black (Pos-info-attacks pos-info))))

(: Pos-info-enemy-attacks (-> Position-info (Listof Attack)))
(define (Pos-info-enemy-attacks pos-info)
  (if (eq? (Position-to-move (Position-info-pos pos-info)) 'white)
      (Attacks-black (Pos-info-attacks pos-info))
      (Attacks-white (Pos-info-attacks pos-info))))

(: Pos-info-sorted-white-attacks (-> Position-info (HashTable Square-location (Listof Attack))))
(define Pos-info-sorted-white-attacks
  (make-Pos-info-getter Position-info-sorted-white-attacks
                        set-Position-info-sorted-white-attacks!
                        (lambda ([pos-info : Position-info])
                          (sort-attacks-by-target (Attacks-white (Pos-info-attacks pos-info))))))

(: Pos-info-sorted-black-attacks (-> Position-info (HashTable Square-location (Listof Attack))))
(define Pos-info-sorted-black-attacks
  (make-Pos-info-getter Position-info-sorted-black-attacks
                        set-Position-info-sorted-black-attacks!
                        (lambda ([pos-info : Position-info])
                          (sort-attacks-by-target (Attacks-black (Pos-info-attacks pos-info))))))

(: Pos-info-defenses (-> Position-info Defenses))
(define Pos-info-defenses
  (make-Pos-info-getter Position-info-defenses
                        set-Position-info-defenses!
                        (lambda ([pos-info : Position-info])
                          (defenses-of-pp (Pos-info-pp pos-info)))))

(: Pos-info-list-of-all-defenses (-> Position-info (Listof Defense)))
(define (Pos-info-list-of-all-defenses pos-info)
  (let ([defenses (Pos-info-defenses pos-info)])
    (append (Defenses-black defenses) (Defenses-white defenses))))

(: Pos-info-defenses-by-target (-> Position-info (HashTable Square-location (Listof Defense))))
(define Pos-info-defenses-by-target
  (make-Pos-info-getter Position-info-defenses-by-target
                        set-Position-info-defenses-by-target!
                        (lambda ([pos-info : Position-info])
                          (sort-defenses-by-target (Pos-info-list-of-all-defenses pos-info)))))

(: defenses-of-location (-> Position-info Square-location (Listof Defense)))
(define (defenses-of-location pos-info loc)
  (hash-ref (Pos-info-defenses-by-target pos-info) loc (lambda () '())))

(: Pos-info-sorted-white-defenses (-> Position-info (HashTable Square-location (Listof Defense))))
(define Pos-info-sorted-white-defenses
  (make-Pos-info-getter Position-info-sorted-white-defenses
                        set-Position-info-sorted-white-defenses!
                        (lambda ([pos-info : Position-info])
                          (sort-defenses-by-target (Defenses-white (Pos-info-defenses pos-info))))))

(: Pos-info-sorted-black-defenses (-> Position-info (HashTable Square-location (Listof Defense))))
(define Pos-info-sorted-black-defenses
  (make-Pos-info-getter Position-info-sorted-black-defenses
                        set-Position-info-sorted-black-defenses!
                        (lambda ([pos-info : Position-info])
                          (sort-defenses-by-target (Defenses-black (Pos-info-defenses pos-info))))))

(: Pos-info-sorted-enemy-defenses (-> Position-info (HashTable Square-location (Listof Defense))))
(define (Pos-info-sorted-enemy-defenses pos-info)
  (if (eq? (Position-to-move (Position-info-pos pos-info)) 'white)
      (Pos-info-sorted-black-defenses pos-info)
      (Pos-info-sorted-white-defenses pos-info)))

(: Pos-info-equivalent-trades (-> Position-info (Listof Square-location)))
(define Pos-info-equivalent-trades
  (make-Pos-info-getter Position-info-equivalent-trades
                        set-Position-info-equivalent-trades!
                        (lambda ([pos-info : Position-info])
                          (locations-with-equivalent-trades (Pos-info-pp pos-info)
                                                            (Pos-info-sorted-white-attacks pos-info)
                                                            (Pos-info-sorted-black-attacks pos-info)
                                                            (Pos-info-sorted-white-defenses pos-info)
                                                            (Pos-info-sorted-black-defenses pos-info)))))

(: Pos-info-en-prise (-> Position-info (Listof Square-location)))
(define Pos-info-en-prise
  (make-Pos-info-getter Position-info-en-prise
                        set-Position-info-en-prise!
                        (lambda ([pos-info : Position-info])
                          (locations-with-possibly-en-prise-piece (Pos-info-pp pos-info)
                                                                  (Pos-info-sorted-white-attacks pos-info)
                                                                  (Pos-info-sorted-black-attacks pos-info)
                                                                  (Pos-info-sorted-white-defenses pos-info)
                                                                  (Pos-info-sorted-black-defenses pos-info)))))

(: Pos-info-enemies-en-prise (-> Position-info (Listof Square-location)))
(define Pos-info-enemies-en-prise
  (make-Pos-info-getter Position-info-enemies-en-prise
                        set-Position-info-enemies-en-prise!
                        (lambda ([pos-info : Position-info])
                          (let ([pos (Position-info-pos pos-info)])
                            (locations-occupied-by-enemy-piece (Position-pp pos)
                                                               (Pos-info-en-prise pos-info)
                                                               (Position-to-move pos))))))

(: Pos-info-own-en-prise (-> Position-info (Listof Square-location)))
(define Pos-info-own-en-prise
  (make-Pos-info-getter Position-info-own-en-prise
                        set-Position-info-own-en-prise!
                        (lambda ([pos-info : Position-info])
                          (let ([pos (Position-info-pos pos-info)])
                            (locations-occupied-by-friendly-piece (Position-pp pos)
                                                                  (Pos-info-en-prise pos-info)
                                                                  (Position-to-move pos))))))

(: Pos-info-switch-to-move (-> Position-info Position-info))
(define (Pos-info-switch-to-move pos-info)
  (make-empty-pos-info (switch-to-move (Position-info-pos pos-info))))
