#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
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
            (> (length candidate) 0))
          (map (string-split s))))
