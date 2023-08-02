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
(require "legal-moves.rkt")

(define positions (positions-from-file "../krr-test/fen_lctrw2_ch8.fen"))
(define movesstrings (file->lines "solutions_lctrw2_ch8.txt"))

(: defends-en-prise? (-> Position Square-location Move Boolean))
(define (defends-en-prise? pos loc move)
  (and (equal? loc (from-of-move move))
       (let* ([new-pos (make-move pos move)]
              [new-loc (to-of-move move)]
              [en-prise-then (locations-with-possibly-en-prise-piece (Position-pp new-pos))])
         (not (member new-loc en-prise-then)))))

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

(: puts-en-prise (-> Position Move (Listof Square-location)))
(define (puts-en-prise pos move)
  (let* ([en-prise-now (locations-with-possibly-en-prise-piece (Position-pp pos))]
         [new-pos (make-move pos move)]
         [en-prise-then (locations-with-possibly-en-prise-piece (Position-pp new-pos))]
         [enemies-en-prise-then (locations-occupied-by-enemy-piece (Position-pp new-pos)
                                                                   en-prise-then
                                                                   (Position-to-move pos))]
         [new-en-prise (filter (lambda ([loc : Square-location])
                                 (not (exists-in en-prise-now
                                                 (lambda ([loc2 : Square-location]) (equal? loc loc2)))))
                               enemies-en-prise-then)])
    new-en-prise))

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

(: locations-with-equivalent-trades (-> Piece-placements (Listof Square-location)))
(define (locations-with-equivalent-trades pp)
  (let* ([attacks (attacks-of-pp pp)]
         [defenses (defenses-of-pp pp)]
         [sorted-white-attacks (sort-attacks-by-target (Attacks-white attacks))]
         [sorted-black-attacks (sort-attacks-by-target (Attacks-black attacks))]
         [sorted-white-defenses (sort-defenses-by-target (Defenses-white defenses))]
         [sorted-black-defenses (sort-defenses-by-target (Defenses-black defenses))]
         [locs : (Listof Square-location) '()])
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

(struct Position-info ([pos : Position]
                       [equivalent-trades : (Option (Listof Square-location))]
                       [en-prise : (Option (Listof Square-location))]
                       [enemies-en-prise : (Option (Listof Square-location))])
  #:transparent
  #:mutable)

(: make-empty-pos-info (-> Position Position-info))
(define (make-empty-pos-info pos)
  (Position-info pos 'none 'none 'none))

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

(: Pos-info-equivalent-trades (-> Position-info (Listof Square-location)))
(define Pos-info-equivalent-trades
  (make-Pos-info-getter Position-info-equivalent-trades
                        set-Position-info-equivalent-trades!
                        (lambda ([pos-info : Position-info])
                          (locations-with-equivalent-trades (Position-pp (Position-info-pos pos-info))))))

(: Pos-info-en-prise (-> Position-info (Listof Square-location)))
(define Pos-info-en-prise
  (make-Pos-info-getter Position-info-en-prise
                        set-Position-info-en-prise!
                        (lambda ([pos-info : Position-info])
                          (locations-with-possibly-en-prise-piece (Position-pp (Position-info-pos pos-info))))))

(: Pos-info-enemies-en-prise (-> Position-info (Listof Square-location)))
(define Pos-info-enemies-en-prise
  (make-Pos-info-getter Position-info-enemies-en-prise
                        set-Position-info-enemies-en-prise!
                        (lambda ([pos-info : Position-info])
                          (let ([pos (Position-info-pos pos-info)])
                            (locations-occupied-by-enemy-piece (Position-pp pos)
                                                               (Pos-info-en-prise pos-info)
                                                               (Position-to-move pos))))))



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
             ((apply r-and (cdr rs)) pos-info move)))))

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

(: candidate-moves-of-tactical-patterns (-> (Listof Pattern-recognizer) (-> Position Integer (Listof Move))))
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

(: candidate-moves-trade-n-capture (-> Position Integer (Listof Move)))
(define candidate-moves-trade-n-capture
  (candidate-moves-of-tactical-patterns
   (list initiates-equivalent-trade?
         initiates-equivalent-trade-or-better?
         (r-or is-mate-in-one?
               initiates-equivalent-trade-or-better?))))

#|
(: candidate-moves-trade-n-capture (-> Position Integer (Listof Move)))
(define (candidate-moves-trade-n-capture pos depth)
  (cond
    [(= depth 0)
     (let* ([moves (legal-moves pos)]
            [equivalent-trades (locations-with-equivalent-trades (Position-pp pos))]
            [offensive-moves
             (filter (lambda ([move : Move])
                       (and (capturing-move? move)
                            (member (to-of-move move) equivalent-trades)))
                     moves)])
       offensive-moves)]
    [(= depth 1)
     (let* ([moves (legal-moves pos)]
            [pp (Position-pp pos)]
            [to-move (Position-to-move pos)]
            [en-prise (locations-with-possibly-en-prise-piece pp)]
            [enemies-en-prise (locations-occupied-by-enemy-piece pp en-prise to-move)]
            [equivalent-trades (locations-with-equivalent-trades pp)]
            [offensive-moves
             (filter (lambda ([move : Move])
                       (and (capturing-move? move)
                            (or (member (to-of-move move) enemies-en-prise)
                                (member (to-of-move move) equivalent-trades))))
                     moves)])
       offensive-moves)]
    [else
          (let* ([moves (legal-moves pos)]
            [pp (Position-pp pos)]
            [to-move (Position-to-move pos)]
            [en-prise (locations-with-possibly-en-prise-piece pp)]
            [enemies-en-prise (locations-occupied-by-enemy-piece pp en-prise to-move)]
            [equivalent-trades (locations-with-equivalent-trades pp)]
            [offensive-moves
             (filter (lambda ([move : Move])
                       (or (and (capturing-move? move)
                                (or (member (to-of-move move) enemies-en-prise)
                                    (member (to-of-move move) equivalent-trades)))
                           (is-mate-in-one? pos move)))
                     moves)])
       offensive-moves)]))
|#

(: candidate-moves (-> Position Integer (Listof Move)))
(define (candidate-moves pos depth)
  (cond
    [(in-check? pos (Position-to-move pos)) (legal-moves pos)]
    [else
     (let* ([moves (legal-moves pos)]
            [to-move (Position-to-move pos)]
            [pp (Position-pp pos)]
            [attacks (attacks-of-pp pp)]
            [defenses (defenses-of-pp pp)]
            [sorted-white-attacks (sort-attacks-by-target (Attacks-white attacks))]
            [sorted-black-attacks (sort-attacks-by-target (Attacks-black attacks))]
            [sorted-white-defenses (sort-defenses-by-target (Defenses-white defenses))]
            [sorted-black-defenses (sort-defenses-by-target (Defenses-black defenses))]
            [sorted-own-attacks (if (eq? to-move 'white) sorted-white-attacks sorted-black-attacks)]
            [sorted-enemy-attacks (if (eq? to-move 'white) sorted-black-attacks sorted-white-attacks)]
            [sorted-own-defenses (if (eq? to-move 'white) sorted-white-defenses sorted-black-defenses)]
            [sorted-enemy-defenses (if (eq? to-move 'white) sorted-black-defenses sorted-white-defenses)]
            [en-prise (locations-with-possibly-en-prise-piece (Position-pp pos))]
            [own-en-prise (locations-occupied-by-friendly-piece pp en-prise to-move)]
            [enemies-en-prise (locations-occupied-by-enemy-piece pp en-prise to-move)]
            [equivalent-trades (locations-with-equivalent-trades (Position-pp pos))]
            [offensive-moves
             (filter (lambda ([move : Move])
                       (or (and (capturing-move? move)
                                (or (member (to-of-move move) enemies-en-prise)
                                    (member (to-of-move move) equivalent-trades)))
                           (exists-in (puts-en-prise pos move)
                                      (lambda ([loc : Square-location])
                                        (is-only-defender? loc sorted-enemy-defenses)))))
                     moves)]
            [defensive-moves
              (filter (lambda ([move : Move])
                        (exists-in own-en-prise
                                   (lambda ([loc : Square-location])
                                     (defends-en-prise? pos loc move))))
                      moves)])
       ;(displayln offensive-moves)
       (remove-duplicates (append offensive-moves defensive-moves)))]))

(: optional-stop? (-> Position Integer Boolean))
(define (optional-stop? pos depth)
#f)
;  (empty? (locations-with-possibly-en-prise-piece (Position-pp pos))))

(: move-search (-> Position (Listof Move-evaluation)))
(define (move-search pos)
  (evaluate-moves-with-optional-stopping evaluate-opening-position candidate-moves-trade-n-capture optional-stop? 4 pos))

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
         [pos-ev-before (evaluate-opening-position pos)])
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

(: perform-test (-> (Listof Position) (Listof String) (Listof Integer)
                    Void))
(define (perform-test positions movesstrings indices)
  (for ([pos positions]
        [movesstr movesstrings] [index indices])
    (let* ([movestrings (string-split movesstr)]
           [calculated-moves (move-search pos)])
      (displayln (format "~a: ~a" index
                         (check-solution pos movestrings calculated-moves))))))
#|
(define positions-to-be-tested positions)
(define movesstrings-to-be-tested movesstrings)
(define indices-to-be-tested (range 1 (+ 1 (length positions))))
|#

(define first 1)
(define last 24)

(define positions-to-be-tested (drop (take positions last) (- first 1)))
(define movesstrings-to-be-tested (drop (take movesstrings last) (- first 1)))
(define indices-to-be-tested (range first (+ last 1)))


(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)

