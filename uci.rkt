#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "min-max-evaluation.rkt")
(require "move-search.rkt")
(require "fen.rkt")
(require "uci-auxiliary.rkt")

(: log-file-path String)
(define log-file-path "/home/andreas/chess/krr/log.txt")

(define current-position (make-initial-position))

(: log (-> String Void))
(define (log s)
  (: out Output-Port)
  (define out (open-output-file log-file-path #:exists 'append))
  (display (format "~a\n" s) out)
  (close-output-port out))

(: log-gui-command (-> String Void))
(define (log-gui-command s)
  (log (format "GUI says: ~a" s)))

(: print-and-log (-> String Void))
(define (print-and-log s)
  (display (format "~a\n" s))
  (flush-output)
  (log s))

(: select-random-element (All (A) (-> (Listof A) A)))
(define (select-random-element l)
  (list-ref l (random (length l))))

(: move->uci-string (-> Move String))
(define (move->uci-string m)
  (: normal-move (-> Square-location Square-location String))
  (define (normal-move from-loc to-loc)
    (format "~a~a"
             (square-location->string from-loc)
             (square-location->string to-loc)))
  (match m
    [(From-to-move from-loc to-loc) (normal-move from-loc to-loc)]
    [(Capture from-loc to-loc) (normal-move from-loc to-loc)]
    [(Double-step from-loc to-loc) (normal-move from-loc to-loc)]
    [(En-passant from-loc to-loc) (normal-move from-loc to-loc)]
    [(Promotion from-loc to-loc piece)
     (format "~a~a" (normal-move from-loc to-loc) (piece->string piece))]
    [(Promotion-with-capture from-loc to-loc piece)
     (format "~a~a" (normal-move from-loc to-loc) (piece->string piece))]
    [(Castle 'white 'queen-side) "e1c1"]
    [(Castle 'white 'king-side) "e1g1"]
    [(Castle 'black 'queen-side) "e8c8"]
    [(Castle 'black 'king-side) "e8g8"]))

(: handle-uci (-> String Boolean))
(define (handle-uci s)
  (if (equal? s "uci")
      (begin
        (print-and-log "id name AH-Chess")
        (print-and-log "id author Andreas Hofmeister")
        (print-and-log "option name Difficulty type spin default 1 min 1 max 10")
        (print-and-log "uciok")
        #t)
      #f))

(: handle-isready (-> String Boolean))
(define (handle-isready s)
  (if (equal? s "isready")
      (begin
        (print-and-log "readyok")
        #t)
      #f))

(: string->movestring-list (-> String (Listof String)))
(define (string->movestring-list s)
  (filter (lambda ([candidate : String])
            (> (string-length candidate) 0))
          (string-split s)))

(: apply-movestring (-> Position String Position))
(define (apply-movestring pos mstr)
  (make-move pos (movestring->move pos mstr)))

(: apply-movestrings (-> Position (Listof String) Position))
(define (apply-movestrings pos mstrs)
  (if (empty? mstrs) pos
      (apply-movestrings (apply-movestring pos (car mstrs))
                         (cdr mstrs))))

(: list-ref-with-default (All (A) (-> (Listof A) Integer A A)))
(define (list-ref-with-default l n default)
  (if (>= n (length l)) default
      (list-ref l n)))

(: handle-position (-> String Boolean))
(define (handle-position str)
  (let ([words (filter (lambda ([word : String])
                         (> (string-length word) 0))
                       (string-split str))])
    (cond
      [(not (equal? (list-ref-with-default words 0 "") "position")) #f]
      [(not (equal? (list-ref-with-default words 1 "") "startpos")) #f]
      [(not (equal? (list-ref-with-default words 2 "") "moves")) #f]
      [else
       (let ([movestrings (cdddr words)])
         (set! current-position
               (apply-movestrings (make-initial-position) movestrings))
         (log (format "DEBUG, new position:\n~a\n~a"
                      (fen-from-position current-position)
                      (pos->string current-position)))
         #t)])))

(: position-evaluation->integer (-> Position-evaluation Integer))
(define (position-evaluation->integer pev)
  (match pev
    [(Normal-evaluation v) v]
    [(Checkmate-evaluation c)
     (match c
       ['black -1000]
       ['white 1000])]
    ['stalemate 0]))

(: move-evaluation->integer (-> Move-evaluation Integer))
(define (move-evaluation->integer mev)
  (match mev
    [(Normal-move-evaluation _ v) v]
    [(Checkmate-move-evaluation move n-moves c)
     (match c
       ['black (+ -1000 n-moves)]
       ['white (- 1000 n-moves)])]
    [(No-move-evaluation pev) (position-evaluation->integer pev)]))

(: cmp-of-player (-> Color (-> Move-evaluation Move-evaluation Boolean)))
(define (cmp-of-player c)
  (match c
    ['black move-evaluation<=]
    ['white
     (lambda ([ev1 : Move-evaluation] [ev2 : Move-evaluation])
       (move-evaluation<= ev2 ev1))]))

(: moves-of-evaluations (-> (Listof Move-evaluation) (Listof Move)))
(define (moves-of-evaluations evs)
  (match evs
    ['() '()]
    [(cons ev tl)
     (match ev
       [(Normal-move-evaluation m _) (cons m (moves-of-evaluations tl))]
       [(Checkmate-move-evaluation m _ _) (cons m (moves-of-evaluations tl))]
       [_ (moves-of-evaluations tl)])]))

(: position-evaluation->string (-> Position-evaluation String))
(define (position-evaluation->string pev)
  (match pev
    [(Normal-evaluation v) (format "~a" v)]
    [(Checkmate-evaluation c)
     (match c
       ['black "Black checkmates"]
       ['white "White checkmates"])]
    ['stalemate "Stalemate"]))

(: move-evaluation->string (-> Move-evaluation String))
(define (move-evaluation->string ev)
  (match ev
    [(Normal-move-evaluation m v) (format "~a: ~a" (move->uci-string m) v)]
    [(Checkmate-move-evaluation m n-moves c)
     (match c
       ['black (format "~a: Black checkmates in ~a" (move->uci-string m) n-moves)]
       ['white (format "~a: White checkmates in ~a" (move->uci-string m) n-moves)])]
    [(No-move-evaluation pev)
     (format "No move?: ~a" (position-evaluation->string pev))]))

(: best-moves (-> Position (Listof Move)))
(define (best-moves pos)
  (let* ([evaluations (evaluate-moves evaluate-opening-position legal-moves 2 pos)]
         [cmp (cmp-of-player (Position-to-move pos))]
         [sorted-evaluations (sort evaluations cmp)]
         [best-value (move-evaluation->integer (car sorted-evaluations))]
         [best-evaluations
          (filter (lambda ([ev : Move-evaluation])
                    (= (move-evaluation->integer ev) best-value))
                  sorted-evaluations)])
    (log "Sorted evaluations:")
    (for ([ev : Move-evaluation sorted-evaluations])
      (log (move-evaluation->string ev)))
    (moves-of-evaluations best-evaluations)))

(: handle-go (-> String Boolean))
(define (handle-go str)
  (let ([words (filter (lambda ([word : String])
                         (> (string-length word) 0))
                       (string-split str))])
    (cond
      [(empty? words) #f]
      [(not (equal? (car words) "go")) #f]
      [else
       (let* ([moves (best-moves current-position)]
              [move (select-random-element moves)])
         (print-and-log (format "bestmove ~a" (move->uci-string move)))
         #t)])))

(: handle-input (-> String Boolean))
(define (handle-input s)
  (cond
    [(handle-uci s) #t]
    [(handle-isready s) #t]
    [(handle-go s) #t]
    [(handle-position s) #t]
    [else #f]))

(: read-line-as-string (-> String))
(define (read-line-as-string)
  (: line (U EOF String))
  (define line (read-line))
  (if (string? line) line "")) 

(: input-output-loop (-> Boolean))
(define (input-output-loop)
  (: input String)
  (define input (read-line-as-string))
  (when (not (equal? "" input))
    (log-gui-command input))
  (cond
    [(equal? input "quit") #t]
    [else
     (handle-input input)
     (input-output-loop)]))

(log (format "uci started on ~a" (seconds->date (current-seconds))))
(: unused Boolean)
(define unused (input-output-loop))


;(handle-position "position startpos moves e2e4 d7d5 b1c3 d5e4 c3e4 d8d5 d2d3 d5e5 g1f3 e5d5 c1e3 a7a5 c2c4 d5c6 f3d4 c6d7 f1e2 b8a6 e1g1 g7g6 d4b5 d7c6 e3d4 e7e5 d4e5 f7f6 e5f4 h7h5 e2f3 a6b8 e4d6 c6d6 f4d6 f8d6 b5d6 c7d6 d1e2 e8f7 f1e1 h5h4 e2e8 f7g7 e8c8 g7f7 c8b7 g8e7 b7a8 e7c6 a8b7 f7f8 f3c6 b8c6 b7c6 h4h3 c6e8 f8g7 e8e7 g7g8 e7d6 h3g2 d6d5 g8g7 d5g2 g7h7 g2h3 h7g7 h3h8 g7h8 a1c1 h8g8 c4c5 g8g7 c5c6 g7f7 c6c7 f6f5 c7c8q")
;(display (pos->string current-position))
;(define pos2 (apply-movestrings current-position (list "e2e4" "b8c6")))
;(display (pos->string pos2))
;(define pos3 (apply-movestrings pos2 (list "b8c6")))
;(display (pos->string pos3))
