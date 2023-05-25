#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")

(provide (all-defined-out))

(: string->piece (-> String Piece))
(define (string->piece s)
  (match s
    ["q" 'queen]
    ["r" 'rook]
    ["n" 'knight]
    ["b" 'bishop]
    ["p" 'pawn]
    ["k" 'king]))

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

(: on-final-rank? (-> Square-location Color Boolean))
(define (on-final-rank? loc c)
  (let ([rank (Square-location-rank loc)])
    (match c
      ['white (= rank 7)]
      ['black (= rank 0)])))

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
