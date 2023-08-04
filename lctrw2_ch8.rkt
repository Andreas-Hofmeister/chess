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
                       [sorted-black-attacks : (Option (HashTable Square-location (Listof Attack)))])

  #:transparent
  #:mutable)

(: make-empty-pos-info (-> Position Position-info))
(define (make-empty-pos-info pos)
  (Position-info pos 'none 'none 'none 'none 'none 'none 'none 'none 'none 'none))

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

(: Pos-info-attacks (-> Position-info Attacks))
(define Pos-info-attacks
  (make-Pos-info-getter Position-info-attacks
                        set-Position-info-attacks!
                        (lambda ([pos-info : Position-info])
                          (attacks-of-pp (Pos-info-pp pos-info)))))

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

(: enemies-put-en-prise (-> Position-info Move (Listof Square-location)))
(define (enemies-put-en-prise pos-info move)
  (let* ([en-prise-now (Pos-info-enemies-en-prise pos-info)]
         [new-pos-info (make-empty-pos-info (make-move (Position-info-pos pos-info) move))]
         [en-prise-then (Pos-info-own-en-prise new-pos-info)]
         [new-en-prise (filter (lambda ([loc : Square-location])
                                 (not (set-member? en-prise-now loc)))
                               en-prise-then)])
    new-en-prise))

(: friendlies-put-en-prise (-> Position-info Move (Listof Square-location)))
(define (friendlies-put-en-prise pos-info move)
  (let* ([en-prise-now (Pos-info-own-en-prise pos-info)]
         [new-pos-info (make-empty-pos-info (make-move (Position-info-pos pos-info) move))]
         [en-prise-then (Pos-info-enemies-en-prise new-pos-info)]
         [new-en-prise (filter (lambda ([loc : Square-location])
                                 (not (set-member? en-prise-now loc)))
                               en-prise-then)])
    new-en-prise))

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

(: puts-friendly-en-prise? Pattern-recognizer)
(define (puts-friendly-en-prise? pos-info move)
  (not (empty? (friendlies-put-en-prise pos-info move))))

(: moves-en-prise-piece? Pattern-recognizer)
(define (moves-en-prise-piece? pos-info move)
  (exists-in (Pos-info-own-en-prise pos-info)
             (lambda ([loc : Square-location])
               (equal? loc (from-of-move move)))))

(define-type Candidate-moves-function (-> Position Integer (Listof Move)))

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
   (list puts-defender-en-prise?
         (r-or moves-en-prise-piece?
               captures-en-prise-piece?)
         (r-or is-mate-in-one?
               captures-en-prise-piece?))))

(: optional-stop? (-> Position Integer Boolean))
(define (optional-stop? pos depth)
#f)
;  (empty? (locations-with-possibly-en-prise-piece (Position-pp pos))))

(: tactical-move-search-with-arsenal (-> Position
                                         (Listof (Pairof Symbol Candidate-moves-function))
                                         Integer Integer
                                         (Pairof Symbol (Listof Move-evaluation))))
(define (tactical-move-search-with-arsenal pos arsenal max-depth improvement-threshold)
  (: iter (-> (Listof (Pairof Symbol Candidate-moves-function))
              Integer
              (Pairof Symbol (Listof Move-evaluation))))
  (define (iter arsenal initial-evaluation)
    (if (empty? arsenal)
        (cons 'none '())
        (let* ([candidate-moves-function (cdr (car arsenal))]
               [candidate-moves-name (car (car arsenal))]
               [move-evs (evaluate-moves-with-optional-stopping
                          evaluate-position
                          candidate-moves-function
                          (lambda (pos depth) #f)
                          max-depth pos)]
               [best-moves (best-evaluations move-evs
                                             (Position-to-move pos))]
               [delta (if (empty? best-moves) 0
                          (- (move-evaluation->integer (car best-moves))
                             initial-evaluation))]
               [color-sgn (if (eq? 'white (Position-to-move pos)) 1 -1)]
               [improvement (* color-sgn delta)])
          (if (>= improvement improvement-threshold)
              (cons candidate-moves-name move-evs)
              (iter (cdr arsenal) initial-evaluation)))))
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
  (list (cons 'trade-and-capture candidate-moves-trade-n-capture)
        (cons 'scare-off-defender candidate-moves-scare-off-defender)
        (cons 'sacrifice-to-remove-defender candidate-moves-sacrifice-to-remove-defender)))

(: perform-test (-> (Listof Position) (Listof String) (Listof Integer)
                    Void))
(define (perform-test positions movesstrings indices)
  (for ([pos positions]
        [movesstr movesstrings] [index indices])
    (let* ([movestrings (string-split movesstr)]
           [tactic-name-and-evs (tactical-move-search-with-arsenal pos arsenal 4 100)]
           [tactic-name (car tactic-name-and-evs)]
           [calculated-moves (cdr tactic-name-and-evs)])
      (displayln (format "~a: ~a (found by ~a)" index
                         (check-solution pos movestrings calculated-moves)
                         tactic-name)))))

(define first 1)
(define last 25)

(define positions-to-be-tested (drop (take positions last) (- first 1)))
(define movesstrings-to-be-tested (drop (take movesstrings last) (- first 1)))
(define indices-to-be-tested (range first (+ last 1)))

(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)

