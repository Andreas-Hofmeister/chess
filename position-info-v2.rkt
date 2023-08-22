#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "check.rkt")
(require "attacks-defenses-v1.rkt")
(require "pawn-moves.rkt")
(require "move-search.rkt")
(provide (all-defined-out))

(: pawn-at-location? (-> Piece-placements Square-location Color Boolean))
(define (pawn-at-location? pp loc c)
  (if (not (location-valid? loc)) #f
      (match (get-square-by-location pp loc)
        [(Occupied-square color piece)
         (and (eq? color c) (eq? piece 'pawn))]
        [_ #f])))

(: is-passed-pawn? (-> Piece-placements Integer Integer Color Boolean))
(define (is-passed-pawn? pp rank-index file-index color)
  (let* ([final-rank (final-rank-of-pawn color)]
         [step (if (eq? color 'white) 1 -1)]
         [rank-indices (range (+ rank-index step) final-rank step)])
    (and (pawn-at-location? pp (Square-location rank-index file-index) color)
         (not (exists-in rank-indices
                         (lambda ([enemy-rank : Integer])
                           (exists-in (list (Square-location enemy-rank file-index)
                                            (Square-location enemy-rank (- file-index 1))
                                            (Square-location enemy-rank (+ file-index 1)))
                                      (lambda ([enemy-loc : Square-location])
                                        (pawn-at-location? pp enemy-loc (opponent-of color))))))))))

(: passed-pawns (-> Piece-placements Color (Listof Square-location)))
(define (passed-pawns pp color)
  (filter (lambda ([loc : Square-location])
            (is-passed-pawn? pp
                             (Square-location-rank loc)
                             (Square-location-file loc)
                             color))
          valid-locations))
                             
(: file-has-passed-pawn? (-> Piece-placements Integer Color Boolean))
(define (file-has-passed-pawn? pp file-index color)
  (let* ([starting-rank (starting-rank-of-pawn color)]
         [final-rank (final-rank-of-pawn color)]
         [step (if (eq? color 'white) 1 -1)]
         [rank-indices (range starting-rank final-rank step)])
    (exists-in rank-indices
               (lambda ([rank-index : Integer])
                 (is-passed-pawn? pp rank-index file-index color)))))

(: files-with-passed-pawn (-> Piece-placements Color (Listof Integer)))
(define (files-with-passed-pawn pp c)
  (filter (lambda ([file-index : Integer])
            (file-has-passed-pawn? pp file-index c))
          (list 0 1 2 3 4 5 6 7)))

(: promotion-squares-of-passed-pawns (-> Piece-placements Color (Listof Square-location)))
(define (promotion-squares-of-passed-pawns pp c)
  (let ([files (files-with-passed-pawn pp c)]
        [promotion-rank (final-rank-of-pawn c)])
    (for/list ([f files])
      (Square-location promotion-rank f))))

(: promotion-threats (-> (Listof Square-location) Color (Listof Square-location)))
(define (promotion-threats passed-pawns-locations color)
  (let ([threatening-rank (match color ['white 6] ['black 1])])
    (filter (lambda ([loc : Square-location])
              (= (Square-location-rank loc) threatening-rank))
            passed-pawns-locations)))

(struct Position-info ([pos : Position]
                       [equivalent-trades : (Option (Listof Square-location))]
                       [en-prise : (Option (Listof Square-location))]
                       [enemies-en-prise : (Option (Listof Square-location))]
                       [own-en-prise : (Option (Listof Square-location))]
                       [defenses : (Option Defenses)]
                       [white-defenses-by-target : (Option (HashTable Square-location (Listof Defense)))]
                       [black-defenses-by-target : (Option (HashTable Square-location (Listof Defense)))]
                       [attacks : (Option Attacks)]
                       [white-attacks-by-target : (Option (HashTable Square-location (Listof Attack)))]
                       [black-attacks-by-target : (Option (HashTable Square-location (Listof Attack)))]
                       [defenses-by-target : (Option (HashTable Square-location (Listof Defense)))]
                       [in-check? : (Option Boolean)]
                       [legal-moves : (Option (Listof Move))]
                       [checkmate-threats : (Option (Listof Move))]
                       [enemy-double-attackers : (Option (Listof Square-location))]
                       [white-passed-pawns : (Option (Listof Square-location))]
                       [black-passed-pawns : (Option (Listof Square-location))]
                       [enemy-promotion-threats : (Option (Listof Square-location))]
                       [white-attacks-by-attacker : (Option (HashTable Square-location (Listof Attack)))]
                       [black-attacks-by-attacker : (Option (HashTable Square-location (Listof Attack)))])
  #:transparent
  #:mutable)

(: make-empty-pos-info (-> Position Position-info))
(define (make-empty-pos-info pos)
  (Position-info pos 'none 'none 'none 'none 'none 'none 'none 'none 'none
                 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none))

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

(: Pos-info-white-passed-pawns (-> Position-info (Listof Square-location)))
(define Pos-info-white-passed-pawns
  (make-Pos-info-getter Position-info-white-passed-pawns
                        set-Position-info-white-passed-pawns!
                        (lambda ([pos-info : Position-info])
                          (passed-pawns (Pos-info-pp pos-info) 'white))))

(: Pos-info-black-passed-pawns (-> Position-info (Listof Square-location)))
(define Pos-info-black-passed-pawns
  (make-Pos-info-getter Position-info-black-passed-pawns
                        set-Position-info-black-passed-pawns!
                        (lambda ([pos-info : Position-info])
                          (passed-pawns (Pos-info-pp pos-info) 'black))))

(: Pos-info-passed-pawns (-> Position-info Color (Listof Square-location)))
(define (Pos-info-passed-pawns pos-info color)
  (if (eq? 'white color)
      (Pos-info-white-passed-pawns pos-info)
      (Pos-info-black-passed-pawns pos-info)))

(: Pos-info-enemy-promotion-threats (-> Position-info (Listof Square-location)))
(define Pos-info-enemy-promotion-threats
  (make-Pos-info-getter Position-info-enemy-promotion-threats
                        set-Position-info-enemy-promotion-threats!
                        (lambda ([pos-info : Position-info])
                          (let ([enemy (opponent-of (Position-to-move (Position-info-pos pos-info)))])
                            (promotion-threats (Pos-info-passed-pawns pos-info enemy) enemy)))))

(: Pos-info-checkmate-threats (-> Position-info (Listof Move)))
(define Pos-info-checkmate-threats
  (make-Pos-info-getter Position-info-checkmate-threats
                        set-Position-info-checkmate-threats!
                        (lambda ([pos-info : Position-info])
                          (let* ([rev-pos (switch-to-move (Position-info-pos pos-info))]
                                 [rev-moves (legal-moves rev-pos)])
                            (moves-of-evaluations (forced-mate-moves (forced-mate-search 5 rev-pos)))))))

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

(: Pos-info-white-attacks-by-target (-> Position-info (HashTable Square-location (Listof Attack))))
(define Pos-info-white-attacks-by-target
  (make-Pos-info-getter Position-info-white-attacks-by-target
                        set-Position-info-white-attacks-by-target!
                        (lambda ([pos-info : Position-info])
                          (sort-attacks-by-target (Attacks-white (Pos-info-attacks pos-info))))))

(: Pos-info-black-attacks-by-target (-> Position-info (HashTable Square-location (Listof Attack))))
(define Pos-info-black-attacks-by-target
  (make-Pos-info-getter Position-info-black-attacks-by-target
                        set-Position-info-black-attacks-by-target!
                        (lambda ([pos-info : Position-info])
                          (sort-attacks-by-target (Attacks-black (Pos-info-attacks pos-info))))))

(: Pos-info-white-attacks-by-attacker (-> Position-info (HashTable Square-location (Listof Attack))))
(define Pos-info-white-attacks-by-attacker
  (make-Pos-info-getter Position-info-white-attacks-by-attacker
                        set-Position-info-white-attacks-by-attacker!
                        (lambda ([pos-info : Position-info])
                          (sort-attacks-by-attacker (Attacks-white (Pos-info-attacks pos-info))))))

(: Pos-info-black-attacks-by-attacker (-> Position-info (HashTable Square-location (Listof Attack))))
(define Pos-info-black-attacks-by-attacker
  (make-Pos-info-getter Position-info-black-attacks-by-attacker
                        set-Position-info-black-attacks-by-attacker!
                        (lambda ([pos-info : Position-info])
                          (sort-attacks-by-attacker (Attacks-black (Pos-info-attacks pos-info))))))

(: Pos-info-enemy-attackers (-> Position-info (HashTable Square-location (Listof Attack))))
(define (Pos-info-enemy-attackers pos-info)
  (if (eq? (Position-to-move (Position-info-pos pos-info)) 'white)
      (Pos-info-black-attacks-by-attacker pos-info) (Pos-info-white-attacks-by-attacker pos-info)))

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

(: Pos-info-white-defenses-by-target (-> Position-info (HashTable Square-location (Listof Defense))))
(define Pos-info-white-defenses-by-target
  (make-Pos-info-getter Position-info-white-defenses-by-target
                        set-Position-info-white-defenses-by-target!
                        (lambda ([pos-info : Position-info])
                          (sort-defenses-by-target (Defenses-white (Pos-info-defenses pos-info))))))

(: Pos-info-black-defenses-by-target (-> Position-info (HashTable Square-location (Listof Defense))))
(define Pos-info-black-defenses-by-target
  (make-Pos-info-getter Position-info-black-defenses-by-target
                        set-Position-info-black-defenses-by-target!
                        (lambda ([pos-info : Position-info])
                          (sort-defenses-by-target (Defenses-black (Pos-info-defenses pos-info))))))

(: Pos-info-sorted-enemy-defenses (-> Position-info (HashTable Square-location (Listof Defense))))
(define (Pos-info-sorted-enemy-defenses pos-info)
  (if (eq? (Position-to-move (Position-info-pos pos-info)) 'white)
      (Pos-info-black-defenses-by-target pos-info)
      (Pos-info-white-defenses-by-target pos-info)))

(: Pos-info-equivalent-trades (-> Position-info (Listof Square-location)))
(define Pos-info-equivalent-trades
  (make-Pos-info-getter Position-info-equivalent-trades
                        set-Position-info-equivalent-trades!
                        (lambda ([pos-info : Position-info])
                          (locations-with-equivalent-trades (Pos-info-pp pos-info)
                                                            (Pos-info-white-attacks-by-target pos-info)
                                                            (Pos-info-black-attacks-by-target pos-info)
                                                            (Pos-info-white-defenses-by-target pos-info)
                                                            (Pos-info-black-defenses-by-target pos-info)))))

(: Pos-info-en-prise (-> Position-info (Listof Square-location)))
(define Pos-info-en-prise
  (make-Pos-info-getter Position-info-en-prise
                        set-Position-info-en-prise!
                        (lambda ([pos-info : Position-info])
                          (locations-with-possibly-en-prise-piece (Pos-info-pp pos-info)
                                                                  (Pos-info-white-attacks-by-target pos-info)
                                                                  (Pos-info-black-attacks-by-target pos-info)
                                                                  (Pos-info-white-defenses-by-target pos-info)
                                                                  (Pos-info-black-defenses-by-target pos-info)))))

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

(: enemy-double-attackers (-> Position-info (Listof Square-location)))
(define (enemy-double-attackers pos-info)
  (let ([attackers (Pos-info-enemy-attackers pos-info)]
        [double-attackers : (Listof Square-location) '()])
    (hash-for-each attackers
                   (lambda ([loc : Square-location]
                            [attacks : (Listof Attack)])
                     (when (>= (length attacks) 2)
                       (set! double-attackers (cons loc double-attackers)))))
    double-attackers))

(define Pos-info-enemy-double-attackers
  (make-Pos-info-getter Position-info-enemy-double-attackers
                        set-Position-info-enemy-double-attackers!
                        enemy-double-attackers))

