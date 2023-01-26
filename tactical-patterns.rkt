#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "check.rkt")
(require "position-etc.rkt")
(require "fen.rkt")

(define-type Tactical-pattern
  (U Checkmate
     Forced-checkmate
     Piece-is-en-prise
     Fork
     Threat))

; The player with color 'color' has checkmated his opponent
(struct Checkmate ([color : Color]) #:transparent)

; Using a sequence of checks, the player with color 'color' can force a checkmate in
; 'number-of-moves' moves, with the first move being 'first-move'
(struct Forced-checkmate ([color : Color]
                          [number-of-moves : Integer]
                          [first-move : Move]) #:transparent)

; The sets of defenders and attackers of a piece are such that the attacker can gain a
; material advantage through a sequence of exchanges.
(struct Piece-is-en-prise ([piece : Piece]
                           [location : Square-location]
                           [exchanges : (Listof Move)]))

; A piece of color 'color' is attacking two or more enemy pieces simultaneously. Whether
; or not the pieces are actually en prise or the fork is somehow defensible is not checked
; by the functions that look for forks and produce values of type Fork.
(struct Fork ([color : Color]
              [piece : Piece]
              [location : Square-location]
              [enemies : (Listof (Pair Piece Square-location))]))

; Several pieces are en prise simultaneously. Examples of how this happens in games
; are forks and discovered attacks. The functions that look for forks and produce
; values of type Fork do not check whether the attacked pieces are actually en prise.
(struct Multi-attack ([attacked-pieces : (Listof Piece-is-en-prise)]))

; If the player with color 'color' were allowed to play the moves 'steps'
; consecutively, then he could produce the tactical pattern 'pattern'.
; Example: (Threat 'white '()
;                  (Forced-checkmate 'white 2
;                                    (Capture (Square-location 5 7) (Square-location 6 7))))
; means that if it were white's turn, white would have a forced checkmate in 2.
(struct Threat ([color : Color] [steps : (Listof Move)] [pattern : Tactical-pattern]))

; Auxiliary function that determines whether a position is a checkmate. Produces a
; list with one Tactical-pattern of type Checkmate when the position is a checkmate and
; an empty list otherwise.
(: checkmate-patterns (-> Position (Listof Tactical-pattern)))
(define (checkmate-patterns pos)
  (let ([number-of-legal-moves (length (legal-moves pos))]
        [to-move (Position-to-move pos)])
    (if (and (= 0 number-of-legal-moves)
             (in-check? pos to-move))
        (list (Checkmate (opponent-of to-move)))
        '())))

; Finds all tactical patterns that are not threats
(: immediate-tactical-patterns (-> Position (Listof Tactical-pattern)))
(define (immediate-tactical-patterns pos)
  (append (checkmate-patterns pos)))

(define-type Piece-status (U Attacks-piece Defends-piece))

; Sometimes a piece only becomes a direct attacker after an initial exchange has been
; made. This is reflected in the 'directness' field. A direct attacker has
; directness = 0 and can capture the enemy piece. If a piece can capture on the
; target square after one exchange, then directness = 1, etc.
; An example where this happens is when a queen and two rooks stands behind one
; another on a file.
(struct Attacks-piece ([target-piece : Piece]
                       [target-location : Square-location]
                       [target-color : Color]
                       [directness : Integer]))

; For an explanation of the 'directness' field, see Attacks-piece above.
(struct Defends-piece ([target-piece : Piece]
                       [target-location : Square-location]
                       [target-color : Color]
                       [directness : Integer]))


(define-type Piece-status-table (HashTable (Pair Piece Square-location) (Setof Piece-status)))

(: make-piece-status-table (-> Piece-status-table))
(define (make-piece-status-table) (make-hash))
(: piece-status-table-set! (-> Piece-status-table (Pair Piece Square-location)
                               (Setof Piece-status)
                      Void))
(define piece-status-table-set! (inst hash-set! (Pair Piece Square-location)
                                      (Setof Piece-status)))
(: piece-status-table-ref (-> Piece-status-table
                              (Pair Piece Square-location)
                              (Setof Piece-status)
                              (Setof Piece-status)))
(define (piece-status-table-ref table key default)
  (if (hash-has-key? table key)
      (hash-ref table key)
      default))

;(: direct-attackers (-> Position (Listof Move) JobTable))
;(define (direct-attackers pos legal-moves)
;  (let* ([result (make-job-table)]
;         [add-job
;          (lambda ([piece : Piece] [location : Square-location] [job : Job])
;            (job-table-set! result (cons piece location)
;                            (cons job (job-table-ref result (cons piece location) '()))))])
;    result))
