#lang typed/racket
(require racket/match)
(require racket/set)

(require "basics.rkt")
(require "fen.rkt")
(require "uci-auxiliary.rkt")
(require "make-move.rkt")
(require "movement-basics.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "min-max-evaluation.rkt")
(require "test-common.rkt")
(require "check.rkt")
(require "pawn-moves.rkt")
(require "legal-moves.rkt")
(require "knight-moves.rkt")

(define positions (positions-from-file "../krr-test/fen_lctrw2_ch8.fen"))
(define movesstrings (file->lines "solutions_lctrw2_ch8.txt"))

(: checkmate-defensive-moves (-> Position (Listof Move) (Listof Move)))
(define (checkmate-defensive-moves pos moves)
  (if (in-check? pos (Position-to-move pos)) moves
      (let* ([rev-pos (switch-to-move pos)]
             [rev-moves (legal-moves rev-pos)]
             [checkmate-threats (moves-of-evaluations (forced-mate-moves (forced-mate-search 1 rev-pos)))]
             [compute-defenses (lambda ([move : Move])
                                 (defensive-moves-for-checkmate-threat pos move moves))]
             [checkmate-threat-defenses (flatten-moves (map compute-defenses checkmate-threats))]
             [result checkmate-threat-defenses])
        result)))

(: equivalent-trade? (-> Piece (Listof Attack) (Listof Defense) Boolean))
(define (equivalent-trade? piece attacks defenses)
  (let* ([balances (sequence-of-material-gain piece
                                              (sort-attacks-by-piece-value attacks)
                                              (sort-defenses-by-piece-value defenses)
                                              true
                                              0)]
         [len (length balances)])
    (or (exists-in (range len)
                   (lambda ([i : Integer])
                     (and (odd? i)
                          (= (list-ref balances i) 0))))
        (and (> len 0)
             (= (list-ref balances (- len 1)) 0)))))

(: locations-with-equivalent-trades (-> Piece-placements
                                        (HashTable Square-location (Listof Attack))
                                        (HashTable Square-location (Listof Attack))
                                        (HashTable Square-location (Listof Defense))
                                        (HashTable Square-location (Listof Defense))
                                        (Listof Square-location)))
(define (locations-with-equivalent-trades pp sorted-white-attacks sorted-black-attacks
                                          sorted-white-defenses sorted-black-defenses)
  (let* ([locs : (Listof Square-location) '()])
    (for ([loc valid-locations])
       (match (get-square-by-location pp loc)
         [(Occupied-square color piece)
          (let* ([sorted-attacks : (HashTable Square-location (Listof Attack))
                                 (if (eq? color 'white) sorted-black-attacks
                                     sorted-white-attacks)]
                 [sorted-defenses : (HashTable Square-location (Listof Defense))
                                  (if (eq? color 'white) sorted-white-defenses
                                      sorted-black-defenses)]
                 [piece-attacks : (Listof Attack) (hash-ref sorted-attacks loc (lambda () '()))]
                 [piece-defenses : (Listof Defense) (hash-ref sorted-defenses loc (lambda () '()))])
            (when (equivalent-trade? piece piece-attacks piece-defenses)
              (set! locs (cons loc locs))))]
         [_ 'nil]))
    locs))

(: is-only-defender? (-> Square-location (HashTable Square-location (Listof Defense)) Boolean))
(define (is-only-defender? defender-loc sorted-defenses)
  (let ([result : Boolean #f])
    (hash-for-each sorted-defenses
                   (lambda ([target-loc : Square-location]
                            [defenses : (Listof Defense)])
                     (when (and (= (length defenses) 1)
                                (equal? (Defense-defender-location (car defenses)) defender-loc))
                       (set! result #t))))
    result))

(: is-defender? (-> Square-location (HashTable Square-location (Listof Defense)) Boolean))
(define (is-defender? defender-loc sorted-defenses)
  (let ([result : Boolean #f])
    (hash-for-each sorted-defenses
                   (lambda ([target-loc : Square-location]
                            [defenses : (Listof Defense)])
                     (when (equal? (Defense-defender-location (car defenses)) defender-loc)
                       (set! result #t))))
    result))

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

(: enemies-put-en-prise (-> Position-info Move (Listof Square-location)))
(define (enemies-put-en-prise pos-info move)
  (let* ([en-prise-now (Pos-info-enemies-en-prise pos-info)]
         [new-pos-info (make-empty-pos-info (make-move (Position-info-pos pos-info) move))]
         [en-prise-then (Pos-info-own-en-prise new-pos-info)]
         [new-en-prise (filter (lambda ([loc : Square-location])
                                 (not (set-member? en-prise-now loc)))
                               en-prise-then)])
    new-en-prise))

(: enemies-attacked (-> Position-info Move (Listof Square-location)))
(define (enemies-attacked pos-info move)
  (let* ([attacks-now (Pos-info-own-attacks pos-info)]
         [new-pos-info (make-empty-pos-info (make-move (Position-info-pos pos-info) move))]
         [attacks-then (Pos-info-enemy-attacks new-pos-info)]
         [new-attacks (filter (lambda ([attack : Attack])
                                 (not (set-member? attacks-now attack)))
                               attacks-then)])
    (map Attack-target-location new-attacks)))

(: friendlies-put-en-prise (-> Position-info Move (Listof Square-location)))
(define (friendlies-put-en-prise pos-info move)
  (let* ([en-prise-now (Pos-info-own-en-prise pos-info)]
         [new-pos-info (make-empty-pos-info (make-move (Position-info-pos pos-info) move))]
         [en-prise-then (Pos-info-enemies-en-prise new-pos-info)]
         [new-en-prise (filter (lambda ([loc : Square-location])
                                 (not (set-member? en-prise-now loc)))
                               en-prise-then)])
    new-en-prise))

(: mate-in-n? (-> Position Integer Boolean))
(define (mate-in-n? pos depth)
  (let ([evs (forced-mate-search depth pos)])
    (exists-in evs (lambda ([ev : Move-evaluation])
                     (match ev
                       [(Checkmate-move-evaluation _ _ _) #t]
                       [_ #f])))))

(: protects-against-checkmate? (-> Position
                                   Square-location
                                   Integer
                                   Boolean))
(define (protects-against-checkmate? pos defender-location mate-depth)
  (match (get-square-by-location (Position-pp pos) defender-location)
    [(Occupied-square color piece)
     (match pos
       [(Position pp to-move pds ca)
        (let* ([new-pp (set-square-by-location! (copy-pp pp) defender-location 'empty-square)]
               [new-pos (Position new-pp (opponent-of color) pds ca)])
          (mate-in-n? new-pos mate-depth))])]
    [_ #f]))

(: knight-guards-promotion-square? (-> Piece-placements Square-location Square-location Boolean))
(define (knight-guards-promotion-square? pp knight-loc promotion-loc)
  (or (equal? knight-loc promotion-loc)
      (set-member? (knight-target-squares knight-loc) promotion-loc)))

(: rook-guards-promotion-square? (-> Piece-placements Square-location Color Square-location Boolean))
(define (rook-guards-promotion-square? pp rook-loc rook-color promotion-loc)
  (or (and (= (Square-location-rank promotion-loc) (Square-location-rank rook-loc))
           (forall-in (locations-between rook-loc promotion-loc)
                      (lambda ([loc : Square-location])
                        (square-empty? pp loc))))
      (and (= (Square-location-file promotion-loc) (Square-location-file rook-loc))
           (let ([locs-between (locations-between rook-loc promotion-loc)]
                 [enemy (opponent-of rook-color)])
             (and (<= (number-such-that locs-between
                                        (lambda ([loc : Square-location])
                                          (square-occupied-by-piece? pp loc 'pawn enemy)))
                      1)
                  (= (number-such-that locs-between
                                       (lambda ([loc : Square-location])
                                         (and (not (square-empty? pp loc))
                                              (not (square-occupied-by-piece? pp loc 'pawn enemy)))))
                     0))))))

(: bishop-guards-promotion-square? (-> Piece-placements Square-location Square-location Boolean))
(define (bishop-guards-promotion-square? pp bishop-loc promotion-loc)
  (and (on-same-diagonal? bishop-loc promotion-loc)
       (forall-in (locations-between bishop-loc promotion-loc)
                  (lambda ([loc : Square-location])
                    (square-empty? pp loc)))))

(: queen-guards-promotion-square? (-> Piece-placements Square-location Color Square-location Boolean))
(define (queen-guards-promotion-square? pp queen-loc queen-color promotion-loc)
  (or (rook-guards-promotion-square? pp queen-loc queen-color promotion-loc)
      (bishop-guards-promotion-square? pp queen-loc promotion-loc)))

(: guards-of-promotion-squares (-> Piece-placements Color (Listof Square-location)))
(define (guards-of-promotion-squares pp guarding-player)
  (let* ([promoting-player (opponent-of guarding-player)]
         [guards : (Listof Square-location) '()]
         [promotion-squares (promotion-squares-of-passed-pawns pp promoting-player)])
    (for ([loc valid-locations])
      (match (get-square-by-location pp loc)
        [(Occupied-square occupied-color occupied-piece)
         (when (and (eq? occupied-color guarding-player)
                    (or (and (eq? occupied-piece 'knight)
                             (exists-in promotion-squares
                                        (lambda ([promotion-loc : Square-location])
                                          (knight-guards-promotion-square? pp loc promotion-loc))))
                        (and (eq? occupied-piece 'rook)
                             (exists-in promotion-squares
                                        (lambda ([promotion-loc : Square-location])
                                          (rook-guards-promotion-square? pp loc guarding-player promotion-loc))))
                        (and (eq? occupied-piece 'bishop)
                             (exists-in promotion-squares
                                        (lambda ([promotion-loc : Square-location])
                                          (bishop-guards-promotion-square? pp loc promotion-loc))))
                        (and (eq? occupied-piece 'queen)
                             (exists-in promotion-squares
                                        (lambda ([promotion-loc : Square-location])
                                          (queen-guards-promotion-square? pp loc guarding-player promotion-loc))))))
           (set! guards (cons loc guards)))]
        [_ 'do-nothing]))
    guards))

(define-type Pattern-recognizer (-> Position-info Move Boolean))

(: r-and (-> Pattern-recognizer * Pattern-recognizer))
(define (r-and . rs)
  (lambda ([pos-info : Position-info] [move : Move])
    (if (empty? rs) #t
        (and ((car rs) pos-info move)
             ((apply r-and (cdr rs)) pos-info move)))))

(: r-or (-> Pattern-recognizer * Pattern-recognizer))
(define (r-or . rs)
  (lambda ([pos-info : Position-info] [move : Move])
    (if (empty? rs) #f
        (or ((car rs) pos-info move)
            ((apply r-or (cdr rs)) pos-info move)))))

(: r-not (-> Pattern-recognizer Pattern-recognizer))
(define (r-not recognizer)
  (lambda ([pos-info : Position-info] [move : Move])
    (not (recognizer pos-info move))))

(: is-mate-in-one? Pattern-recognizer)
(define (is-mate-in-one? pos-info move)
  (let* ([new-pos (make-move (Position-info-pos pos-info) move)])
    (and (in-check? new-pos (Position-to-move new-pos))
         (empty? (legal-moves new-pos)))))

(: is-capturing-move? Pattern-recognizer)
(define (is-capturing-move? pos-info move)
  (capturing-move? move))

(: to-en-prise? Pattern-recognizer)
(define (to-en-prise? pos-info move)
  (set-member? (Pos-info-enemies-en-prise pos-info) (to-of-move move)))

(: to-equivalent-trade? Pattern-recognizer)
(define (to-equivalent-trade? pos-info move)
  (set-member? (Pos-info-equivalent-trades pos-info) (to-of-move move)))

(: initiates-equivalent-trade? Pattern-recognizer)
(define (initiates-equivalent-trade? pos-info move)
  (and (capturing-move? move)
       (set-member? (Pos-info-equivalent-trades pos-info) (to-of-move move))))

(: initiates-equivalent-trade-or-better? Pattern-recognizer)
(define initiates-equivalent-trade-or-better?
  (r-and is-capturing-move?
         (r-or to-en-prise? to-equivalent-trade?)))

(: captures-en-prise-piece? Pattern-recognizer)
(define captures-en-prise-piece?
  (r-and is-capturing-move? to-en-prise?))

(: puts-defender-en-prise? Pattern-recognizer)
(define (puts-defender-en-prise? pos-info move)
  (exists-in (enemies-put-en-prise pos-info move)
             (lambda ([loc : Square-location])
               (is-defender? loc (Pos-info-sorted-enemy-defenses pos-info)))))

(: attacks-defender? Pattern-recognizer)
(define (attacks-defender? pos-info move)
  (exists-in (enemies-attacked pos-info move)
             (lambda ([loc : Square-location])
               (is-defender? loc (Pos-info-sorted-enemy-defenses pos-info)))))

(: attacks-guard-of-promotion-square? Pattern-recognizer)
(define (attacks-guard-of-promotion-square? pos-info move)
  (let* ([attacking-player (Position-to-move (Position-info-pos pos-info))]
         [guarding-player (opponent-of attacking-player)]
         [guards (guards-of-promotion-squares (Pos-info-pp pos-info) guarding-player)])
    (or (and (capturing-move? move)
             (set-member? guards (to-of-move move)))
        (exists-in (enemies-attacked pos-info move)
                   (lambda ([loc : Square-location])
                     (set-member? guards loc))))))

(: moves-guard-of-promotion-square? Pattern-recognizer)
(define (moves-guard-of-promotion-square? pos-info move)
  (let* ([guarding-player (Position-to-move (Position-info-pos pos-info))]
         [guards (guards-of-promotion-squares (Pos-info-pp pos-info) guarding-player)])
    (set-member? guards (from-of-move move))))

(: puts-friendly-en-prise? Pattern-recognizer)
(define (puts-friendly-en-prise? pos-info move)
  (not (empty? (friendlies-put-en-prise pos-info move))))

(: is-checking-move? Pattern-recognizer)
(define (is-checking-move? pos-info move)
  (puts-opponent-in-check? (Position-info-pos pos-info) move))

(: is-in-check? Pattern-recognizer)
(define (is-in-check? pos-info move)
  (Pos-info-in-check? pos-info))

(: is-promotion-move? Pattern-recognizer)
(define (is-promotion-move? pos-info move)
  (promotion-move? move))

(: moves-en-prise-piece? Pattern-recognizer)
(define (moves-en-prise-piece? pos-info move)
  (exists-in (Pos-info-own-en-prise pos-info)
             (lambda ([loc : Square-location])
               (equal? loc (from-of-move move)))))

(: captures-piece-with-overworked-defenders? Pattern-recognizer)
(define (captures-piece-with-overworked-defenders? pos-info move)
  (if (not (capturing-move? move)) #f
      (let ([defenses (defenses-of-location pos-info (to-of-move move))]
            [pos-after-capture (make-move (Position-info-pos pos-info) move)])
        (forall-in defenses
                   (lambda ([defense : Defense])
                     (protects-against-checkmate? pos-after-capture
                                                  (Defense-defender-location defense)
                                                  5))))))
(: defends-against-checkmate? Pattern-recognizer)
(define (defends-against-checkmate? pos-info move)
  (let ([threats (Pos-info-checkmate-threats pos-info)]
        [pos (Position-info-pos pos-info)])
    (if (empty? threats) #f
        (or (king-move? pos move)
            (move-by-piece-adjacent-to-king? pos move)
            (exists-in threats
                       (lambda ([threatened-move : Move])
                         (or (move-defends-square? pos move (to-of-move threatened-move))
                             (move-blocks-move? pos move threatened-move)
                             (captures-on-square? move (from-of-move threatened-move)))))
            (puts-opponent-in-check? pos move)))))

(define-type Candidate-moves-function (-> Position Integer (Listof Move)))
(define-type Optional-stop-function (-> Position Integer Boolean))

(: candidate-moves-of-tactical-patterns (-> (Listof Pattern-recognizer) Candidate-moves-function))
(define (candidate-moves-of-tactical-patterns patterns)
  (cond
    [(empty? patterns) (lambda ([pos : Position] [depth : Integer]) '())]
    [(= (length patterns) 1)
     (lambda ([pos : Position] [depth : Integer])
       (let ([pos-info (make-empty-pos-info pos)])
         (filter (lambda ([move : Move])
                   ((car patterns) pos-info move))
                 (legal-moves pos))))]
    [else
     (let ([rec-candidates (candidate-moves-of-tactical-patterns (cdr patterns))])
       (lambda ([pos : Position] [depth : Integer])
         (if (= depth 0)
             (let ([pos-info (make-empty-pos-info pos)])
               (filter (lambda ([move : Move]) ((car patterns) pos-info move))
                       (legal-moves pos)))
             (rec-candidates pos (- depth 1)))))]))

(: candidate-moves-trade-n-capture Candidate-moves-function)
(define candidate-moves-trade-n-capture
  (candidate-moves-of-tactical-patterns
   (list initiates-equivalent-trade?
         initiates-equivalent-trade-or-better?
         (r-or is-mate-in-one?
               initiates-equivalent-trade-or-better?))))

(: candidate-moves-scare-off-defender Candidate-moves-function)
(define candidate-moves-scare-off-defender
  (candidate-moves-of-tactical-patterns
   (list (r-and puts-defender-en-prise?
                (r-not puts-friendly-en-prise?))
         (r-or moves-en-prise-piece?
               captures-en-prise-piece?)
         (r-or is-mate-in-one?
               captures-en-prise-piece?))))

(: candidate-moves-sacrifice-to-remove-defender Candidate-moves-function)
(define candidate-moves-sacrifice-to-remove-defender
  (candidate-moves-of-tactical-patterns
   (list attacks-defender?
         (r-or moves-en-prise-piece?
               captures-en-prise-piece?)
         (r-or is-mate-in-one?
               defends-against-checkmate?
               captures-en-prise-piece?))))

(: candidate-moves-capture-piece-with-overworked-defenders Candidate-moves-function)
(define candidate-moves-capture-piece-with-overworked-defenders
  (candidate-moves-of-tactical-patterns
   (list captures-piece-with-overworked-defenders?
         (r-or is-in-check?
               is-checking-move?
               captures-en-prise-piece?))))

(: candidate-moves-sacrifice-to-remove-promotion-guard Candidate-moves-function)
(define candidate-moves-sacrifice-to-remove-promotion-guard
  (candidate-moves-of-tactical-patterns
   (list attacks-guard-of-promotion-square?
         (r-or is-in-check?
               moves-guard-of-promotion-square?
               captures-en-prise-piece?)
         (r-or is-promotion-move?
               captures-en-prise-piece?)
         (r-or is-mate-in-one?
               is-promotion-move?
               captures-en-prise-piece?))))

;  (empty? (locations-with-possibly-en-prise-piece (Position-pp pos))))

(: never-stop Optional-stop-function)
(define (never-stop pos depth) #f)

(: stop-when-ahead-and-no-immediate-threats (-> Integer Optional-stop-function))
(define (stop-when-ahead-and-no-immediate-threats threshold)
  (lambda ([pos : Position] [depth : Integer])
    (let* ([ev (position-evaluation->integer (evaluate-position pos))]
           [player-sgn (if (eq? 'white (Position-to-move pos)) 1 -1)]
           [pos-info (make-empty-pos-info pos)])
      (and (>= (* player-sgn ev) threshold)
           (not (in-check? pos (Position-to-move pos)))
           (empty? (Pos-info-own-en-prise pos-info))))))

(struct Arsenal ([names : (Listof Symbol)]
                 [functions : (Listof Candidate-moves-function)]
                 [depths : (Listof Integer)]
                 [optional-stops : (Listof Optional-stop-function)]))

(: Arsenal-cdr (-> Arsenal Arsenal))
(define (Arsenal-cdr arsenal)
  (Arsenal (cdr (Arsenal-names arsenal))
           (cdr (Arsenal-functions arsenal))
           (cdr (Arsenal-depths arsenal))
           (cdr (Arsenal-optional-stops arsenal))))

(: Arsenal-empty? (-> Arsenal Boolean))
(define (Arsenal-empty? arsenal)
  (empty? (Arsenal-functions arsenal)))

(struct Tactical-search-result ([function-name : Symbol]
                                [move-evaluations : (Listof Move-evaluation)]
                                [improvement : Integer]))

(: tactical-move-search-with-arsenal (-> Position
                                         Arsenal
                                         Integer
                                         Tactical-search-result))
(define (tactical-move-search-with-arsenal pos arsenal improvement-threshold)
  (: iter (-> Arsenal
              Integer
              Tactical-search-result))
  (define (iter arsenal initial-evaluation)
    (if (Arsenal-empty? arsenal)
        (Tactical-search-result 'none '() 0)
        (let* ([candidate-moves-function (car (Arsenal-functions arsenal))]
               [candidate-moves-name (car (Arsenal-names arsenal))]
               [max-depth (car (Arsenal-depths arsenal))]
               [hard-threshold (* 2 improvement-threshold)]
               [optional-stop (car (Arsenal-optional-stops arsenal))]
               [move-evs (evaluate-moves-with-optional-stopping
                          evaluate-position
                          candidate-moves-function
                          optional-stop
                          max-depth pos)]
               [best-moves (best-evaluations move-evs
                                             (Position-to-move pos))]
               [delta (if (empty? best-moves) 0
                          (- (move-evaluation->integer (car best-moves))
                             initial-evaluation))]
               [color-sgn (if (eq? 'white (Position-to-move pos)) 1 -1)]
               [improvement (* color-sgn delta)])
          (if (>= improvement hard-threshold)
              (Tactical-search-result candidate-moves-name move-evs improvement)
              (let* ([potentially-better-solution (iter (Arsenal-cdr arsenal) initial-evaluation)]
                     [potentially-higher-improvement (Tactical-search-result-improvement potentially-better-solution)])
                (cond
                  [(and (>= potentially-higher-improvement improvement-threshold)
                        (> potentially-higher-improvement improvement))
                   potentially-better-solution]
                  [(>= improvement improvement-threshold)
                   (Tactical-search-result candidate-moves-name move-evs improvement)]
                  [else
                   (Tactical-search-result 'none '() 0)]))))))
  (iter arsenal (position-evaluation->integer (evaluate-position pos))))

(: evs->string (-> (Listof Move-evaluation) String))
(define (evs->string evs)
  (let ([moves (moves-of-evaluations evs)]
        [vs (map move-evaluation->integer evs)]
        [result : (Listof String) '()])
    (for ([move moves]
          [v vs])
      (set! result (cons (format "~a: ~a" (move->uci-string move) v) result)))
    (string-join (reverse result) ", ")))

(: check-solution (-> Position (Listof String) (Listof Move-evaluation)
                      String))
(define (check-solution pos move-strs solution-moves)
  (let* ([move (movestring->move pos (car move-strs))]
         [best-solutions (best-evaluations solution-moves
                                           (Position-to-move pos))]
         [pos-ev-before (evaluate-position pos)])
    (cond
      [(> (length best-solutions) 1)
       (format "More than one solution found: ~a" best-solutions)]
      [(empty? best-solutions)
       (format "No solutions found")]
      [else
       (if (not (move-in-evaluations? move best-solutions))
           (format "Wrong move: ~a"
                   (evs->string (sort-evaluations solution-moves (Position-to-move pos))))
           (format "Ok: ~a (before: ~a)" (evs->string best-solutions) (position-evaluation->integer pos-ev-before)))])))

(define arsenal
  (Arsenal
   (list 'trade-and-capture
         'scare-off-defender
         'sacrifice-to-remove-defender
         'capture-piece-with-overworked-defenders
         'sacrifice-to-remove-promotion-guard)
   (list candidate-moves-trade-n-capture
         candidate-moves-scare-off-defender
         candidate-moves-sacrifice-to-remove-defender
         candidate-moves-capture-piece-with-overworked-defenders
         candidate-moves-sacrifice-to-remove-promotion-guard)
   (list 4
         4
         5
         7
         5)
   (list never-stop
         never-stop
         never-stop
         (stop-when-ahead-and-no-immediate-threats 100)
         never-stop)))

(: perform-test (-> (Listof Position) (Listof String) (Listof Integer)
                    Void))
(define (perform-test positions movesstrings indices)
  (for ([pos positions]
        [movesstr movesstrings] [index indices])
    (let* ([movestrings (string-split movesstr)]
           [search-result (tactical-move-search-with-arsenal pos arsenal 100)]
           [tactic-name (Tactical-search-result-function-name search-result)]
           [calculated-moves (Tactical-search-result-move-evaluations search-result)]
           [improvement (Tactical-search-result-improvement search-result)])
      (displayln (format "~a: ~a (improvement: ~a, found by: ~a)" index
                         (check-solution pos movestrings calculated-moves)
                         improvement
                         tactic-name)))))

(define first 1)
(define last 60)

(define positions-to-be-tested (drop (take positions last) (- first 1)))
(define movesstrings-to-be-tested (drop (take movesstrings last) (- first 1)))
(define indices-to-be-tested (range first (+ last 1)))

(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)


(: collect-best-moves (-> Position Candidate-moves-function Optional-stop-function
                          Integer Integer (Listof Move)))
(define (collect-best-moves pos candidate-moves-function optional-stop current-depth max-depth)
  (if (> current-depth max-depth) '()
      (let* ([depth-adjusted-candidates-f
              (lambda ([pos : Position] [depth : Integer])
                (candidate-moves-function pos (+ depth current-depth)))]
             [move-evs (evaluate-moves-with-optional-stopping
                        evaluate-position
                        depth-adjusted-candidates-f
                        optional-stop
                        (- max-depth current-depth) pos)]
             [best-evs (best-evaluations move-evs
                                         (Position-to-move pos))]
             [best-moves (moves-of-evaluations best-evs)])
        (if (empty? best-moves) '()
            (let* ([best-move (car best-moves)]
                   [new-pos (make-move pos best-move)])
              (cons best-move (collect-best-moves new-pos candidate-moves-function optional-stop
                                                  (+ current-depth 1) max-depth)))))))


(define test-pos (pos-from-fen "1B6/kp5p/pqp2p2/5bp1/8/1P2Q2P/P4PPK/8 b - - 1 1"))
(define test-current-depth 1)
(define test-max-depth 5)
(define test-candidate-moves candidate-moves-sacrifice-to-remove-defender)
(define test-stop never-stop)
#|
(for ([move (collect-best-moves test-pos test-candidate-moves test-stop test-current-depth test-max-depth)])
  (set! test-pos (make-move test-pos move))
  (set! test-current-depth (+ test-current-depth 1))
  (displayln (format "~a (ev: ~a) (optional-stop: ~a)"
                     (move->uci-string move)
                     (position-evaluation->integer (evaluate-position test-pos))
                     (test-stop test-pos test-current-depth))))
|#
