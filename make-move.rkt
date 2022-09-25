#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")

(provide (all-defined-out))

(: make-from-to-move-pp (-> Piece-placements Square-location Square-location
                            Piece-placements))
(define (make-from-to-move-pp pp from to)
  (let ([from-square (get-square-by-location pp from)]
        [new-pp (copy-pp pp)])
      (set-square-by-location! new-pp to from-square)
      (set-square-by-location! new-pp from 'empty-square)))

(: en-passant-step? (-> Square-location Square-location Color Boolean))
(define (en-passant-step? from to c)
  (let ([from-rank (Square-location-rank from)]
        [from-file (Square-location-file from)]
        [to-rank (Square-location-rank to)]
        [to-file (Square-location-file to)])
  (match c
    ['white (and (= from-rank 4) (= to-rank 5) (= (difference from-file to-file) 1))]
    ['black (and (= from-rank 3) (= to-rank 2) (= (difference from-file to-file) 1))])))

(: en-passant-capture-rank (-> Color Integer))
(define (en-passant-capture-rank c)
  (match c
    ['white 4]
    ['black 3]))

(: remove-en-passant-capture! (-> Piece-placements Square-location Square-location
                                  Piece-placements))
(define (remove-en-passant-capture! pp from to)
  (let ([from-rank (Square-location-rank from)]
        [to-file (Square-location-file to)])
    (if (or (= from-rank (en-passant-capture-rank 'white))
            (= from-rank (en-passant-capture-rank 'black)))
        (set-square! pp from-rank to-file 'empty-square)
        pp)))

(: make-en-passant-move-pp (-> Piece-placements Square-location Square-location
                               Piece-placements))
(define (make-en-passant-move-pp before from to)
  (remove-en-passant-capture! (make-from-to-move-pp before from to) from to))

(: promotion-rank (-> Color Integer))
(define (promotion-rank c)
  (match c
    ['white 7]
    ['black 0]))

(: make-promotion-move-pp (-> Piece-placements Square-location Square-location Piece
                              Piece-placements))
(define (make-promotion-move-pp before from to piece)
  (: make-new-pp (-> Color Piece-placements))
  (define (make-new-pp c)
    (set-square-by-location! (make-from-to-move-pp before from to)
                               to
                               (Occupied-square c piece)))
  (let ([to-rank (Square-location-rank to)])
    (cond
      [(= to-rank (promotion-rank 'white)) (make-new-pp 'white)]
      [(= to-rank (promotion-rank 'black)) (make-new-pp 'black)]
      [else before])))

(: make-castling-move-pp-aux (-> Piece-placements Color Integer Integer
                                 Integer Integer Piece-placements))
(define (make-castling-move-pp-aux pp c rank-index new-king-file old-rook-file
                                   new-rook-file)
  (let ([new-pp (copy-pp pp)])
    (set-square! new-pp rank-index 4 'empty-square)
    (set-square! new-pp rank-index old-rook-file 'empty-square)
    (set-square! new-pp rank-index new-king-file (Occupied-square c 'king))
    (set-square! new-pp rank-index new-rook-file (Occupied-square c 'rook))))

(: make-castling-move-pp (-> Piece-placements Color Castling-type
                             Piece-placements))
(define (make-castling-move-pp pp c ct)
  (match* (c ct)
    [('white 'king-side) (make-castling-move-pp-aux pp 'white 0 6 7 5)]
    [('white 'queen-side) (make-castling-move-pp-aux pp 'white 0 2 0 3)]
    [('black 'king-side) (make-castling-move-pp-aux pp 'black 7 6 7 5)]
    [('black 'queen-side) (make-castling-move-pp-aux pp 'black 7 2 0 3)]))

(: initial-rook-location (-> Color Castling-type Square-location))
(define (initial-rook-location c ctype)
  (match* (c ctype)
    [('white 'king-side) (Square-location 0 7)]
    [('white 'queen-side) (Square-location 0 0)]
    [('black 'king-side) (Square-location 7 7)]
    [('black 'queen-side) (Square-location 7 0)]))

(: remove-castling-availability (-> Castling-availability
                                    (Listof Castling-availability)
                                    (Listof Castling-availability)))
(define (remove-castling-availability cavl cavls)
  (filter (lambda ([c : Castling-availability]) (not (equal? c cavl))) cavls))

(: remove-castling-availabilities (-> Color
                                    (Listof Castling-availability)
                                    (Listof Castling-availability)))
(define (remove-castling-availabilities color cavls)
  (filter (lambda ([cavl : Castling-availability])
            (not (equal? color (Castling-availability-color cavl))))
          cavls))


(: initial-rook-move? (-> Castling-type Piece-placements
                          (Listof Castling-availability) Move Color
                          Boolean))
(define (initial-rook-move? ctype pp cavls move c)
  (let ([from (from-of-move move)])
    (match (get-square-by-location pp from)
      [(Occupied-square square-c piece)
       (and (equal? piece 'rook)
            (equal? square-c c)
            (equal? (initial-rook-location c ctype) from)
            (exists-in cavls (curry equal? (Castling-availability ctype c))))]
      [_ #f])))

(: make-from-to-move
   (-> Position Move Piece-placements Color
       (Option Pawn-double-step) (Listof Castling-availability)
       Square-location Square-location
       Position))
(define (make-from-to-move before move pp c pds cavls from to)
  (: position-for-initial-rook-move (-> Castling-type Position))
  (define (position-for-initial-rook-move ctype)
    (Position (make-from-to-move-pp pp from to) (opponent-of c) 'none
              (remove-castling-availability (Castling-availability ctype c) cavls)))
  (match (get-square-by-location pp from)
    [(Occupied-square square-c piece)
     (match piece
       ['rook
        (cond
          [(initial-rook-move? 'queen-side pp cavls move c)
           (position-for-initial-rook-move 'queen-side)]
          [(initial-rook-move? 'king-side pp cavls move c)
           (position-for-initial-rook-move 'king-side)]
          [else (Position (make-from-to-move-pp pp from to) (opponent-of c) 'none
                           cavls)])]
       ['king
        (Position (make-from-to-move-pp pp from to) (opponent-of c) 'none
                           (remove-castling-availabilities c cavls))]
       [_ before])]))

         