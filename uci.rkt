#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")

(provide (all-defined-out))

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

(: on-final-rank? (-> Square-location Color Boolean))
(define (on-final-rank? loc c)
  (let ([rank (Square-location-rank loc)])
    (match c
      ['white (= rank 7)]
      ['black (= rank 0)])))

(: from-to-or-capture-move (-> Piece-placements Square-location Square-location Move))
(define (from-to-or-capture-move pp from-loc to-loc)
  (let ([to-square (get-square-by-location pp to-loc)])
    (match to-square
      [(Occupied-square _ _) (Capture from-loc to-loc)]
      [_ (From-to-move from-loc to-loc)])))

(: en-passant-move? (-> Square Square-location Square-location Boolean))
(define (en-passant-move? to-square from-loc to-loc)
  (let ([from-file (Square-location-file from-loc)]
        [to-file (Square-location-file to-loc)])
    (match to-square
      [(Occupied-square _ _) #f]
      [_ (not (= from-file to-file))])))

(: double-step? (-> Square-location Square-location Boolean))
(define (double-step? from-loc to-loc)
  (let ([from-rank (Square-location-rank from-loc)]
        [to-rank (Square-location-rank to-loc)])
    (= (abs (- from-rank to-rank)) 2)))

(: string->piece (-> String Piece))
(define (string->piece s)
  (match s
    ['q 'queen]
    ['r 'rook]
    ['n 'knight]
    ['b 'bishop]
    ['p 'pawn]
    ['k 'king]))

(: movestring->move (-> Position String Move))
(define (movestring->move pos mstr)
  (let* ([pp (Position-pp pos)]
         [from-loc (Square-location (string->rank-index (substring mstr 1 2))
                                    (string->file-index (substring mstr 0 1)))]
         [to-loc (Square-location (string->rank-index (substring mstr 3 4))
                                  (string->file-index (substring mstr 2 3)))]
         [to-square (get-square-by-location pp to-loc)]
         [from-square (get-square-by-location pp from-loc)])
    (match from-square
      [(Occupied-square c 'pawn)
       (cond
         [(on-final-rank? to-loc c)
          (let ([p (string->piece (substring mstr 4 5))])
            (match to-square
              [(Occupied-square _ _) (Promotion-with-capture from-loc to-loc p)]
              [_ (Promotion from-loc to-loc p)]))]
         [(en-passant-move? to-square from-loc to-loc)
          (En-passant from-loc to-loc)]
         [(double-step? from-loc to-loc)
          (Double-step from-loc to-loc)]
         [else (from-to-or-capture-move pp from-loc to-loc)])]
      [(Occupied-square c 'king)
       (match mstr
         ["e1c1" (Castle 'white 'queen-side)]
         ["e1g1" (Castle 'white 'king-side)]
         ["e8c8" (Castle 'black 'queen-side)]
         ["e8g8" (Castle 'black 'king-side)]
         [_ (from-to-or-capture-move pp from-loc to-loc)])]
      [_ (from-to-or-capture-move pp from-loc to-loc)])))

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
         (log (format "DEBUG, new position:\n~a" (pos->string current-position)))
         #t)])))

(: position-evaluation->integer (-> Position-evaluation Integer))
(define (position-evaluation->integer pev)
  (match pev
    [(Normal-evaluation v) v]
    [(Checkmate c)
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
    ['white move-evaluation<=]
    ['black
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
    [(Checkmate c)
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
  (let* ([evaluations (evaluate-moves 3 pos)]
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
  (log-gui-command input)
  (cond
    [(equal? input "quit") #t]
    [else
     (handle-input input)
     (input-output-loop)]))

(: unused Boolean)
(define unused (input-output-loop))
