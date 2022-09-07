
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : nat -> nat -> bool **)

let rec eqb n m =
  match n with
  | O -> (match m with
          | O -> True
          | S _ -> False)
  | S n' -> (match m with
             | O -> False
             | S m' -> eqb n' m')

(** val leb : nat -> nat -> bool **)

let rec leb n m =
  match n with
  | O -> True
  | S n' -> (match m with
             | O -> False
             | S m' -> leb n' m')

(** val ltb : nat -> nat -> bool **)

let ltb n m =
  leb (S n) m

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t -> fold_left f t (f a0 b)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> (match f x with
            | True -> x::(filter f l0)
            | False -> filter f l0)

type color =
| White
| Black

(** val opponent_of : color -> color **)

let opponent_of = function
| White -> Black
| Black -> White

(** val ceq : color -> color -> bool **)

let ceq c1 c2 =
  match c1 with
  | White -> (match c2 with
              | White -> True
              | Black -> False)
  | Black -> (match c2 with
              | White -> False
              | Black -> True)

type piece =
| Pawn
| Rook
| Knight
| Bishop
| Queen
| King

(** val eqPiece : piece -> piece -> bool **)

let eqPiece p1 p2 =
  match p1 with
  | Pawn -> (match p2 with
             | Pawn -> True
             | _ -> False)
  | Rook -> (match p2 with
             | Rook -> True
             | _ -> False)
  | Knight -> (match p2 with
               | Knight -> True
               | _ -> False)
  | Bishop -> (match p2 with
               | Bishop -> True
               | _ -> False)
  | Queen -> (match p2 with
              | Queen -> True
              | _ -> False)
  | King -> (match p2 with
             | King -> True
             | _ -> False)

type square =
| Empty
| Occupied of color * piece

(** val eqSq : square -> square -> bool **)

let eqSq s1 s2 =
  match s1 with
  | Empty -> (match s2 with
              | Empty -> True
              | Occupied (_, _) -> False)
  | Occupied (c1, p1) ->
    (match s2 with
     | Empty -> False
     | Occupied (c2, p2) ->
       (match eqPiece p1 p2 with
        | True -> ceq c1 c2
        | False -> False))

type file =
| Squares of square * square * square * square * square * square * square
   * square

(** val empty_file : file **)

let empty_file =
  Squares (Empty, Empty, Empty, Empty, Empty, Empty, Empty, Empty)

type piecePlacements =
| Files of file * file * file * file * file * file * file * file

(** val empty_pp : piecePlacements **)

let empty_pp =
  Files (empty_file, empty_file, empty_file, empty_file, empty_file,
    empty_file, empty_file, empty_file)

(** val initial_file_with_piece : piece -> file **)

let initial_file_with_piece p =
  Squares ((Occupied (White, p)), (Occupied (White, Pawn)), Empty, Empty,
    Empty, Empty, (Occupied (Black, Pawn)), (Occupied (Black, p)))

(** val initial_file_a : file **)

let initial_file_a =
  initial_file_with_piece Rook

(** val initial_file_b : file **)

let initial_file_b =
  initial_file_with_piece Knight

(** val initial_file_c : file **)

let initial_file_c =
  initial_file_with_piece Bishop

(** val initial_file_d : file **)

let initial_file_d =
  initial_file_with_piece Queen

(** val initial_file_e : file **)

let initial_file_e =
  initial_file_with_piece King

(** val initial_file_f : file **)

let initial_file_f =
  initial_file_with_piece Bishop

(** val initial_file_g : file **)

let initial_file_g =
  initial_file_with_piece Knight

(** val initial_file_h : file **)

let initial_file_h =
  initial_file_with_piece Rook

(** val initial_pp : piecePlacements **)

let initial_pp =
  Files (initial_file_a, initial_file_b, initial_file_c, initial_file_d,
    initial_file_e, initial_file_f, initial_file_g, initial_file_h)

type fileName =
| Fa
| Fb
| Fc
| Fd
| Fe
| Ff
| Fg
| Fh

type rankName =
| R1
| R2
| R3
| R4
| R5
| R6
| R7
| R8

(** val index_to_rank : nat -> rankName **)

let index_to_rank = function
| O -> R1
| S n ->
  (match n with
   | O -> R2
   | S n0 ->
     (match n0 with
      | O -> R3
      | S n1 ->
        (match n1 with
         | O -> R4
         | S n2 ->
           (match n2 with
            | O -> R5
            | S n3 ->
              (match n3 with
               | O -> R6
               | S n4 -> (match n4 with
                          | O -> R7
                          | S _ -> R8))))))

(** val index_to_file : nat -> fileName **)

let index_to_file = function
| O -> Fa
| S n ->
  (match n with
   | O -> Fb
   | S n0 ->
     (match n0 with
      | O -> Fc
      | S n1 ->
        (match n1 with
         | O -> Fd
         | S n2 ->
           (match n2 with
            | O -> Fe
            | S n3 ->
              (match n3 with
               | O -> Ff
               | S n4 -> (match n4 with
                          | O -> Fg
                          | S _ -> Fh))))))

(** val get_file : piecePlacements -> fileName -> file **)

let get_file pp fn =
  let Files (a, b, c, d, e, f, g, h) = pp in
  (match fn with
   | Fa -> a
   | Fb -> b
   | Fc -> c
   | Fd -> d
   | Fe -> e
   | Ff -> f
   | Fg -> g
   | Fh -> h)

(** val get_square : piecePlacements -> rankName -> fileName -> square **)

let get_square pp rn fn =
  let Squares (s1, s2, s3, s4, s5, s6, s7, s8) = get_file pp fn in
  (match rn with
   | R1 -> s1
   | R2 -> s2
   | R3 -> s3
   | R4 -> s4
   | R5 -> s5
   | R6 -> s6
   | R7 -> s7
   | R8 -> s8)

(** val get_square_by_index : piecePlacements -> nat -> nat -> square **)

let get_square_by_index pp rn fn =
  get_square pp (index_to_rank rn) (index_to_file fn)

(** val rank_index_valid : nat -> bool **)

let rank_index_valid ri =
  leb ri (S (S (S (S (S (S (S O)))))))

(** val file_index_valid : nat -> bool **)

let file_index_valid =
  rank_index_valid

(** val indices_valid : nat -> nat -> bool **)

let indices_valid ri fi =
  match file_index_valid fi with
  | True -> rank_index_valid ri
  | False -> False

(** val set_file : piecePlacements -> fileName -> file -> piecePlacements **)

let set_file pp fn file0 =
  let Files (a, b, c, d, e, f, g, h) = pp in
  (match fn with
   | Fa -> Files (file0, b, c, d, e, f, g, h)
   | Fb -> Files (a, file0, c, d, e, f, g, h)
   | Fc -> Files (a, b, file0, d, e, f, g, h)
   | Fd -> Files (a, b, c, file0, e, f, g, h)
   | Fe -> Files (a, b, c, d, file0, f, g, h)
   | Ff -> Files (a, b, c, d, e, file0, g, h)
   | Fg -> Files (a, b, c, d, e, f, file0, h)
   | Fh -> Files (a, b, c, d, e, f, g, file0))

(** val set_square_in_file : rankName -> file -> square -> file **)

let set_square_in_file r f s =
  let Squares (s1, s2, s3, s4, s5, s6, s7, s8) = f in
  (match r with
   | R1 -> Squares (s, s2, s3, s4, s5, s6, s7, s8)
   | R2 -> Squares (s1, s, s3, s4, s5, s6, s7, s8)
   | R3 -> Squares (s1, s2, s, s4, s5, s6, s7, s8)
   | R4 -> Squares (s1, s2, s3, s, s5, s6, s7, s8)
   | R5 -> Squares (s1, s2, s3, s4, s, s6, s7, s8)
   | R6 -> Squares (s1, s2, s3, s4, s5, s, s7, s8)
   | R7 -> Squares (s1, s2, s3, s4, s5, s6, s, s8)
   | R8 -> Squares (s1, s2, s3, s4, s5, s6, s7, s))

(** val set_square :
    piecePlacements -> rankName -> fileName -> square -> piecePlacements **)

let set_square pp rn fn s =
  set_file pp fn (set_square_in_file rn (get_file pp fn) s)

(** val set_square_by_index :
    piecePlacements -> nat -> nat -> square -> piecePlacements **)

let set_square_by_index pp ri fi s =
  match indices_valid ri fi with
  | True -> set_square pp (index_to_rank ri) (index_to_file fi) s
  | False -> pp

type squareLocation =
| Loc of nat * nat

(** val rank_of_loc : squareLocation -> nat **)

let rank_of_loc = function
| Loc (rank, _) -> rank

(** val file_of_loc : squareLocation -> nat **)

let file_of_loc = function
| Loc (_, file0) -> file0

(** val get_square_by_location :
    piecePlacements -> squareLocation -> square **)

let get_square_by_location pp = function
| Loc (rn, fn) -> get_square_by_index pp rn fn

(** val eqSL : squareLocation -> squareLocation -> bool **)

let eqSL l1 l2 =
  let Loc (rank1, file1) = l1 in
  let Loc (rank2, file2) = l2 in
  (match eqb rank1 rank2 with
   | True -> eqb file1 file2
   | False -> False)

type pawnDoubleStep =
| DoubleStepRankFile of nat * nat

type castlingType =
| QueenSide
| KingSide

(** val ctypeeq : castlingType -> castlingType -> bool **)

let ctypeeq ctype1 ctype2 =
  match ctype1 with
  | QueenSide -> (match ctype2 with
                  | QueenSide -> True
                  | KingSide -> False)
  | KingSide -> (match ctype2 with
                 | QueenSide -> False
                 | KingSide -> True)

type castlingAvailability =
| Cavl of castlingType * color

(** val cavleq : castlingAvailability -> castlingAvailability -> bool **)

let cavleq cavl1 cavl2 =
  let Cavl (ctype1, c1) = cavl1 in
  let Cavl (ctype2, c2) = cavl2 in
  (match ctypeeq ctype1 ctype2 with
   | True -> ceq c1 c2
   | False -> False)

(** val initial_cavls : castlingAvailability list **)

let initial_cavls =
  (Cavl (QueenSide, White))::((Cavl (KingSide, White))::((Cavl (QueenSide,
    Black))::((Cavl (KingSide, White))::[])))

type position =
| Posn of piecePlacements * color * pawnDoubleStep option
   * castlingAvailability list

(** val initial_position : position **)

let initial_position =
  Posn (initial_pp, White, None, initial_cavls)

(** val get_piece_placements : position -> piecePlacements **)

let get_piece_placements = function
| Posn (pp, _, _, _) -> pp

(** val get_to_move : position -> color **)

let get_to_move = function
| Posn (_, toMove, _, _) -> toMove

(** val is_square_empty_rank_file : nat -> nat -> piecePlacements -> bool **)

let is_square_empty_rank_file rank file0 pp =
  match get_square_by_index pp rank file0 with
  | Empty -> True
  | Occupied (_, _) -> False

(** val is_square_empty : squareLocation -> piecePlacements -> bool **)

let is_square_empty loc pp =
  let Loc (r, f) = loc in is_square_empty_rank_file r f pp

(** val occupied_by_enemy_piece :
    nat -> nat -> piecePlacements -> color -> bool **)

let occupied_by_enemy_piece r f pp c =
  match indices_valid r f with
  | True ->
    (match get_square_by_index pp r f with
     | Empty -> False
     | Occupied (oc, _) -> (match ceq oc c with
                            | True -> False
                            | False -> True))
  | False -> False

(** val is_square_occupied_by_enemy_piece :
    squareLocation -> piecePlacements -> color -> bool **)

let is_square_occupied_by_enemy_piece l pp c =
  let Loc (rank, file0) = l in occupied_by_enemy_piece rank file0 pp c

(** val difference : nat -> nat -> nat **)

let difference i j =
  match ltb i j with
  | True -> sub j i
  | False -> sub i j

(** val locations_equal : squareLocation -> squareLocation -> bool **)

let locations_equal loc1 loc2 =
  let Loc (x1, y1) = loc1 in
  let Loc (x2, y2) = loc2 in
  (match eqb x1 x2 with
   | True -> eqb y1 y2
   | False -> False)

(** val append_forall : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let append_forall f l =
  let f_inner = fun acc x -> app (f x) acc in fold_left f_inner l []

(** val for_accumulate :
    (nat -> 'a1) -> (nat -> bool) -> nat -> nat -> 'a1 list **)

let rec for_accumulate f cond min_i max_i = match max_i with
| O -> (match cond O with
        | True -> (f O)::[]
        | False -> [])
| S n ->
  (match eqb max_i min_i with
   | True -> (match cond max_i with
              | True -> (f max_i)::[]
              | False -> [])
   | False ->
     (match cond max_i with
      | True -> (f max_i)::(for_accumulate f cond min_i n)
      | False -> for_accumulate f cond min_i n))

(** val squares_on_same_rank : squareLocation -> squareLocation list **)

let squares_on_same_rank = function
| Loc (rank, file0) ->
  let make_square = fun n -> Loc (rank, n) in
  for_accumulate make_square (fun n -> negb (eqb n file0)) O (S (S (S (S (S
    (S (S O)))))))

(** val squares_on_same_file : squareLocation -> squareLocation list **)

let squares_on_same_file = function
| Loc (rank, file0) ->
  let make_square = fun n -> Loc (n, file0) in
  for_accumulate make_square (fun n -> negb (eqb n rank)) O (S (S (S (S (S (S
    (S O)))))))

(** val is_location_valid : squareLocation -> bool **)

let is_location_valid = function
| Loc (r, f) ->
  (match leb r (S (S (S (S (S (S (S O))))))) with
   | True -> leb f (S (S (S (S (S (S (S O)))))))
   | False -> False)

(** val valid_locations : squareLocation list **)

let valid_locations =
  (Loc (O, O))::((Loc (O, (S O)))::((Loc (O, (S (S O))))::((Loc (O, (S (S (S
    O)))))::((Loc (O, (S (S (S (S O))))))::((Loc (O, (S (S (S (S (S
    O)))))))::((Loc (O, (S (S (S (S (S (S O))))))))::((Loc (O, (S (S (S (S (S
    (S (S O)))))))))::((Loc ((S O), O))::((Loc ((S O), (S O)))::((Loc ((S O),
    (S (S O))))::((Loc ((S O), (S (S (S O)))))::((Loc ((S O), (S (S (S (S
    O))))))::((Loc ((S O), (S (S (S (S (S O)))))))::((Loc ((S O), (S (S (S (S
    (S (S O))))))))::((Loc ((S O), (S (S (S (S (S (S (S O)))))))))::((Loc ((S
    (S O)), O))::((Loc ((S (S O)), (S O)))::((Loc ((S (S O)), (S (S
    O))))::((Loc ((S (S O)), (S (S (S O)))))::((Loc ((S (S O)), (S (S (S (S
    O))))))::((Loc ((S (S O)), (S (S (S (S (S O)))))))::((Loc ((S (S O)), (S
    (S (S (S (S (S O))))))))::((Loc ((S (S O)), (S (S (S (S (S (S (S
    O)))))))))::((Loc ((S (S (S O))), O))::((Loc ((S (S (S O))), (S
    O)))::((Loc ((S (S (S O))), (S (S O))))::((Loc ((S (S (S O))), (S (S (S
    O)))))::((Loc ((S (S (S O))), (S (S (S (S O))))))::((Loc ((S (S (S O))),
    (S (S (S (S (S O)))))))::((Loc ((S (S (S O))), (S (S (S (S (S (S
    O))))))))::((Loc ((S (S (S O))), (S (S (S (S (S (S (S O)))))))))::((Loc
    ((S (S (S (S O)))), O))::((Loc ((S (S (S (S O)))), (S O)))::((Loc ((S (S
    (S (S O)))), (S (S O))))::((Loc ((S (S (S (S O)))), (S (S (S
    O)))))::((Loc ((S (S (S (S O)))), (S (S (S (S O))))))::((Loc ((S (S (S (S
    O)))), (S (S (S (S (S O)))))))::((Loc ((S (S (S (S O)))), (S (S (S (S (S
    (S O))))))))::((Loc ((S (S (S (S O)))), (S (S (S (S (S (S (S
    O)))))))))::((Loc ((S (S (S (S (S O))))), O))::((Loc ((S (S (S (S (S
    O))))), (S O)))::((Loc ((S (S (S (S (S O))))), (S (S O))))::((Loc ((S (S
    (S (S (S O))))), (S (S (S O)))))::((Loc ((S (S (S (S (S O))))), (S (S (S
    (S O))))))::((Loc ((S (S (S (S (S O))))), (S (S (S (S (S O)))))))::((Loc
    ((S (S (S (S (S O))))), (S (S (S (S (S (S O))))))))::((Loc ((S (S (S (S
    (S O))))), (S (S (S (S (S (S (S O)))))))))::((Loc ((S (S (S (S (S (S
    O)))))), O))::((Loc ((S (S (S (S (S (S O)))))), (S O)))::((Loc ((S (S (S
    (S (S (S O)))))), (S (S O))))::((Loc ((S (S (S (S (S (S O)))))), (S (S (S
    O)))))::((Loc ((S (S (S (S (S (S O)))))), (S (S (S (S O))))))::((Loc ((S
    (S (S (S (S (S O)))))), (S (S (S (S (S O)))))))::((Loc ((S (S (S (S (S (S
    O)))))), (S (S (S (S (S (S O))))))))::((Loc ((S (S (S (S (S (S O)))))),
    (S (S (S (S (S (S (S O)))))))))::((Loc ((S (S (S (S (S (S (S O))))))),
    O))::((Loc ((S (S (S (S (S (S (S O))))))), (S O)))::((Loc ((S (S (S (S (S
    (S (S O))))))), (S (S O))))::((Loc ((S (S (S (S (S (S (S O))))))), (S (S
    (S O)))))::((Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S
    O))))))::((Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S (S
    O)))))))::((Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S (S (S
    O))))))))::((Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S (S (S (S
    O)))))))))::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val locations_neq : squareLocation -> squareLocation -> bool **)

let locations_neq loc1 loc2 =
  let Loc (rnk1, fl1) = loc1 in
  let Loc (rnk2, fl2) = loc2 in
  (match negb (eqb rnk1 rnk2) with
   | True -> True
   | False -> negb (eqb fl1 fl2))

(** val adjacent_squares : squareLocation -> squareLocation list **)

let adjacent_squares loc = match loc with
| Loc (r, f) ->
  filter (locations_neq loc)
    (filter is_location_valid ((Loc (r, (add f (S O))))::((Loc
      ((add r (S O)), (add f (S O))))::((Loc ((add r (S O)), f))::((Loc
      ((add r (S O)), (sub f (S O))))::((Loc (r, (sub f (S O))))::((Loc
      ((sub r (S O)), (sub f (S O))))::((Loc ((sub r (S O)), f))::((Loc
      ((sub r (S O)), (add f (S O))))::[])))))))))

(** val exists_in : 'a1 list -> ('a1 -> bool) -> bool **)

let rec exists_in l f =
  match l with
  | [] -> False
  | x::xs -> (match f x with
              | True -> True
              | False -> exists_in xs f)

(** val find_piece :
    position -> color -> piece -> squareLocation list -> squareLocation list **)

let rec find_piece pos c p = function
| [] -> []
| s::rlocs ->
  let Loc (r, f) = s in
  (match eqSq (get_square_by_index (get_piece_placements pos) r f) (Occupied
           (c, p)) with
   | True -> (Loc (r, f))::(find_piece pos c p rlocs)
   | False -> find_piece pos c p rlocs)

type move =
| FromTo of squareLocation * squareLocation
| Capture of squareLocation * squareLocation
| DoubleStep of squareLocation * squareLocation
| EnPassant of squareLocation * squareLocation
| Promotion of squareLocation * squareLocation * piece
| PromotionWithCapture of squareLocation * squareLocation * piece
| Castle of color * castlingType

(** val fromOfMove : move -> squareLocation **)

let fromOfMove = function
| FromTo (from, _) -> from
| Capture (from, _) -> from
| DoubleStep (from, _) -> from
| EnPassant (from, _) -> from
| Promotion (from, _, _) -> from
| PromotionWithCapture (from, _, _) -> from
| Castle (c, _) ->
  (match c with
   | White -> Loc (O, (S (S (S (S O)))))
   | Black -> Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S O))))))

(** val toOfMove : move -> squareLocation **)

let toOfMove = function
| FromTo (_, to0) -> to0
| Capture (_, to0) -> to0
| DoubleStep (_, to0) -> to0
| EnPassant (_, to0) -> to0
| Promotion (_, to0, _) -> to0
| PromotionWithCapture (_, to0, _) -> to0
| Castle (c, castling_type) ->
  (match c with
   | White ->
     (match castling_type with
      | QueenSide -> Loc (O, (S (S O)))
      | KingSide -> Loc (O, (S (S (S (S (S (S O))))))))
   | Black ->
     (match castling_type with
      | QueenSide -> Loc ((S (S (S (S (S (S (S O))))))), (S (S O)))
      | KingSide ->
        Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S (S (S O)))))))))

(** val is_capturing_move : move -> bool **)

let is_capturing_move = function
| Capture (_, _) -> True
| PromotionWithCapture (_, _, _) -> True
| _ -> False

type horizontalDirection =
| Left
| Right

type verticalDirection =
| Up
| Down

type horizontalStep =
| HStep of horizontalDirection * nat

type verticalStep =
| VStep of verticalDirection * nat

type vector =
| VectorHV of horizontalStep * verticalStep

(** val vector_from_a_to_b : squareLocation -> squareLocation -> vector **)

let vector_from_a_to_b a b =
  let Loc (r_a, f_a) = a in
  let Loc (r_b, f_b) = b in
  let rank_step =
    match leb r_a r_b with
    | True -> VStep (Up, (sub r_b r_a))
    | False -> VStep (Down, (sub r_a r_b))
  in
  let file_step =
    match leb f_a f_b with
    | True -> HStep (Right, (sub f_b f_a))
    | False -> HStep (Left, (sub f_a f_b))
  in
  VectorHV (file_step, rank_step)

(** val vector_length : vector -> nat **)

let vector_length = function
| VectorHV (hstep, vstep) ->
  let HStep (_, n) = hstep in let VStep (_, m) = vstep in add n m

(** val one_step_along_vector_and_location :
    squareLocation -> vector -> (vector, squareLocation) prod **)

let one_step_along_vector_and_location l v =
  let Loc (r, f) = l in
  let VectorHV (hstep, vstep) = v in
  let HStep (dh, n0) = hstep in
  (match dh with
   | Left ->
     (match n0 with
      | O ->
        let VStep (dv, n) = vstep in
        (match dv with
         | Up ->
           (match n with
            | O -> Pair ((VectorHV ((HStep (dh, O)), (VStep (dv, O)))), l)
            | S m ->
              Pair ((VectorHV ((HStep (dh, O)), (VStep (Up, m)))), (Loc
                ((add r (S O)), f))))
         | Down ->
           (match n with
            | O -> Pair ((VectorHV ((HStep (dh, O)), (VStep (dv, O)))), l)
            | S m ->
              Pair ((VectorHV ((HStep (dh, O)), (VStep (Down, m)))), (Loc
                ((sub r (S O)), f)))))
      | S n ->
        let VStep (dv, n1) = vstep in
        (match dv with
         | Up ->
           (match n1 with
            | O ->
              Pair ((VectorHV ((HStep (Left, n)), (VStep (dv, O)))), (Loc (r,
                (sub f (S O)))))
            | S m ->
              Pair ((VectorHV ((HStep (Left, n)), (VStep (Up, m)))), (Loc
                ((add r (S O)), (sub f (S O))))))
         | Down ->
           (match n1 with
            | O ->
              Pair ((VectorHV ((HStep (Left, n)), (VStep (dv, O)))), (Loc (r,
                (sub f (S O)))))
            | S m ->
              Pair ((VectorHV ((HStep (Left, n)), (VStep (Down, m)))), (Loc
                ((sub r (S O)), (sub f (S O))))))))
   | Right ->
     (match n0 with
      | O ->
        let VStep (dv, n) = vstep in
        (match dv with
         | Up ->
           (match n with
            | O -> Pair ((VectorHV ((HStep (dh, O)), (VStep (dv, O)))), l)
            | S m ->
              Pair ((VectorHV ((HStep (dh, O)), (VStep (Up, m)))), (Loc
                ((add r (S O)), f))))
         | Down ->
           (match n with
            | O -> Pair ((VectorHV ((HStep (dh, O)), (VStep (dv, O)))), l)
            | S m ->
              Pair ((VectorHV ((HStep (dh, O)), (VStep (Down, m)))), (Loc
                ((sub r (S O)), f)))))
      | S n ->
        let VStep (dv, n1) = vstep in
        (match dv with
         | Up ->
           (match n1 with
            | O ->
              Pair ((VectorHV ((HStep (Right, n)), (VStep (dv, O)))), (Loc
                (r, (add f (S O)))))
            | S m ->
              Pair ((VectorHV ((HStep (Right, n)), (VStep (Up, m)))), (Loc
                ((add r (S O)), (add f (S O))))))
         | Down ->
           (match n1 with
            | O ->
              Pair ((VectorHV ((HStep (Right, n)), (VStep (dv, O)))), (Loc
                (r, (add f (S O)))))
            | S m ->
              Pair ((VectorHV ((HStep (Right, n)), (VStep (Down, m)))), (Loc
                ((sub r (S O)), (add f (S O)))))))))

(** val are_squares_along_vector_empty :
    piecePlacements -> squareLocation -> vector -> bool **)

let rec are_squares_along_vector_empty pp start v =
  match eqb (vector_length v) O with
  | True -> True
  | False ->
    let Pair (a, b) = one_step_along_vector_and_location start v in
    (match is_square_empty start pp with
     | True -> are_squares_along_vector_empty pp b a
     | False -> False)

(** val apply_hstep : horizontalStep -> squareLocation -> squareLocation **)

let apply_hstep s loc =
  let HStep (d, n) = s in
  (match d with
   | Left -> let Loc (r, f) = loc in Loc (r, (sub f n))
   | Right -> let Loc (r, f) = loc in Loc (r, (add f n)))

(** val apply_vstep : verticalStep -> squareLocation -> squareLocation **)

let apply_vstep s loc =
  let VStep (d, n) = s in
  (match d with
   | Up -> let Loc (r, f) = loc in Loc ((add r n), f)
   | Down -> let Loc (r, f) = loc in Loc ((sub r n), f))

(** val apply_vector : vector -> squareLocation -> squareLocation **)

let apply_vector v loc =
  let VectorHV (hstep, vstep) = v in apply_vstep vstep (apply_hstep hstep loc)

(** val are_squares_between_empty :
    piecePlacements -> squareLocation -> squareLocation -> bool **)

let are_squares_between_empty pp loc1 loc2 =
  let Pair (v, start) =
    one_step_along_vector_and_location loc1 (vector_from_a_to_b loc1 loc2)
  in
  are_squares_along_vector_empty pp start v

(** val move_to_square_on_rfd :
    position -> color -> squareLocation -> squareLocation -> move option **)

let move_to_square_on_rfd pos c fromL toL =
  let Posn (pp, _, _, _) = pos in
  (match match negb (eqSL fromL toL) with
         | True -> are_squares_between_empty pp fromL toL
         | False -> False with
   | True ->
     (match is_square_empty toL pp with
      | True -> Some (FromTo (fromL, toL))
      | False ->
        (match is_square_occupied_by_enemy_piece toL pp c with
         | True -> Some (Capture (fromL, toL))
         | False -> None))
   | False -> None)

(** val moves_to_square_on_rfd_list :
    position -> color -> squareLocation -> squareLocation -> move list **)

let moves_to_square_on_rfd_list pos c fromL toL =
  match move_to_square_on_rfd pos c fromL toL with
  | Some move0 -> move0::[]
  | None -> []

(** val squares_along_direction_aux :
    squareLocation -> horizontalDirection -> verticalDirection -> nat ->
    squareLocation list **)

let rec squares_along_direction_aux l hd vd = function
| O -> []
| S n ->
  let Loc (rank, file0) = l in
  (match hd with
   | Left ->
     (match vd with
      | Up ->
        let l1 = Loc ((add rank (S O)), (sub file0 (S O))) in
        l1::(squares_along_direction_aux l1 Left Up n)
      | Down ->
        let l1 = Loc ((sub rank (S O)), (sub file0 (S O))) in
        l1::(squares_along_direction_aux l1 Left Down n))
   | Right ->
     (match vd with
      | Up ->
        let l1 = Loc ((add rank (S O)), (add file0 (S O))) in
        l1::(squares_along_direction_aux l1 Right Up n)
      | Down ->
        let l1 = Loc ((sub rank (S O)), (add file0 (S O))) in
        l1::(squares_along_direction_aux l1 Right Down n)))

(** val squares_along_direction :
    squareLocation -> horizontalDirection -> verticalDirection ->
    squareLocation list **)

let squares_along_direction l hd vd =
  let Loc (rank, file0) = l in
  let hsteps =
    match hd with
    | Left -> file0
    | Right -> sub (S (S (S (S (S (S (S O))))))) file0
  in
  let vsteps =
    match vd with
    | Up -> sub (S (S (S (S (S (S (S O))))))) rank
    | Down -> rank
  in
  squares_along_direction_aux l hd vd (min hsteps vsteps)

(** val squares_on_same_diagonal : squareLocation -> squareLocation list **)

let squares_on_same_diagonal l =
  app (squares_along_direction l Right Up)
    (squares_along_direction l Left Down)

(** val squares_on_same_antidiagonal :
    squareLocation -> squareLocation list **)

let squares_on_same_antidiagonal l =
  app (squares_along_direction l Right Down)
    (squares_along_direction l Left Up)

(** val does_vector_stay_within_boundaries :
    vector -> squareLocation -> bool **)

let does_vector_stay_within_boundaries v = function
| Loc (x, y) ->
  let VectorHV (hstep, vstep) = v in
  let HStep (d, n) = hstep in
  (match d with
   | Left ->
     let VStep (d0, m) = vstep in
     (match d0 with
      | Up ->
        (match leb n y with
         | True -> leb (add x m) (S (S (S (S (S (S (S O)))))))
         | False -> False)
      | Down -> (match leb n y with
                 | True -> leb m x
                 | False -> False))
   | Right ->
     let VStep (d0, m) = vstep in
     (match d0 with
      | Up ->
        (match leb (add x m) (S (S (S (S (S (S (S O))))))) with
         | True -> leb (add y n) (S (S (S (S (S (S (S O)))))))
         | False -> False)
      | Down ->
        (match leb m x with
         | True -> leb (add y n) (S (S (S (S (S (S (S O)))))))
         | False -> False)))

(** val target_squares :
    squareLocation -> vector list -> squareLocation list **)

let rec target_squares from = function
| [] -> []
| v::rvs ->
  (match does_vector_stay_within_boundaries v from with
   | True -> (apply_vector v from)::(target_squares from rvs)
   | False -> target_squares from rvs)

(** val advance_pawn : color -> nat -> nat **)

let advance_pawn c rank_index =
  match c with
  | White -> add rank_index (S O)
  | Black -> sub rank_index (S O)

(** val starting_rank_of_pawn : color -> nat **)

let starting_rank_of_pawn = function
| White -> S O
| Black -> S (S (S (S (S (S O)))))

(** val final_rank_of_pawn : color -> nat **)

let final_rank_of_pawn = function
| White -> S (S (S (S (S (S (S O))))))
| Black -> O

(** val pawn_forward_moves :
    squareLocation -> color -> position -> move list **)

let pawn_forward_moves pawn_loc c = function
| Posn (pp, _, _, _) ->
  let Loc (r, f) = pawn_loc in
  let new_r = advance_pawn c r in
  (match match indices_valid r f with
         | True -> indices_valid new_r f
         | False -> False with
   | True ->
     (match match is_square_empty_rank_file new_r f pp with
            | True -> negb (eqb new_r (final_rank_of_pawn c))
            | False -> False with
      | True -> (FromTo (pawn_loc, (Loc (new_r, f))))::[]
      | False -> [])
   | False -> [])

(** val pawn_captures : squareLocation -> color -> position -> move list **)

let pawn_captures pawn_loc c = function
| Posn (pp, _, _, _) ->
  let Loc (r, f) = pawn_loc in
  (match indices_valid r f with
   | True ->
     let new_r = advance_pawn c r in
     let left_capture =
       match match leb (S O) f with
             | True -> occupied_by_enemy_piece new_r (sub f (S O)) pp c
             | False -> False with
       | True -> (Capture (pawn_loc, (Loc (new_r, (sub f (S O))))))::[]
       | False -> []
     in
     let right_capture =
       match match leb f (S (S (S (S (S (S O)))))) with
             | True -> occupied_by_enemy_piece new_r (add f (S O)) pp c
             | False -> False with
       | True -> (Capture (pawn_loc, (Loc (new_r, (add f (S O))))))::[]
       | False -> []
     in
     (match match eqb r (final_rank_of_pawn c) with
            | True -> True
            | False -> eqb new_r (final_rank_of_pawn c) with
      | True -> []
      | False -> app left_capture right_capture)
   | False -> [])

(** val pawn_double_steps :
    squareLocation -> color -> position -> move list **)

let pawn_double_steps pawn_loc c = function
| Posn (pp, _, _, _) ->
  let Loc (r, f) = pawn_loc in
  (match indices_valid r f with
   | True ->
     (match eqb (starting_rank_of_pawn c) r with
      | True ->
        let step1r = advance_pawn c r in
        let step2r = advance_pawn c step1r in
        (match match is_square_empty_rank_file step1r f pp with
               | True -> is_square_empty_rank_file step2r f pp
               | False -> False with
         | True -> (DoubleStep (pawn_loc, (Loc (step2r, f))))::[]
         | False -> [])
      | False -> [])
   | False -> [])

(** val en_passant_moves :
    squareLocation -> color -> position -> move list **)

let en_passant_moves pawn_loc c pos =
  let Loc (r, f) = pawn_loc in
  (match indices_valid r f with
   | True ->
     let Posn (_, toMove, pawnDoubleStep0, _) = pos in
     (match pawnDoubleStep0 with
      | Some p ->
        let DoubleStepRankFile (dsr, dsf) = p in
        (match match ceq c toMove with
               | True ->
                 (match eqb dsr r with
                  | True -> indices_valid (advance_pawn toMove r) dsf
                  | False -> False)
               | False -> False with
         | True ->
           (match eqb (difference f dsf) (S O) with
            | True ->
              (EnPassant (pawn_loc, (Loc ((advance_pawn toMove r), dsf))))::[]
            | False -> [])
         | False -> [])
      | None -> [])
   | False -> [])

(** val pawn_forward_promotions :
    squareLocation -> color -> position -> move list **)

let pawn_forward_promotions pawn_loc c = function
| Posn (pp, _, _, _) ->
  let Loc (r, f) = pawn_loc in
  let new_r = advance_pawn c r in
  (match match indices_valid r f with
         | True -> indices_valid new_r f
         | False -> False with
   | True ->
     (match match is_square_empty_rank_file new_r f pp with
            | True -> eqb new_r (final_rank_of_pawn c)
            | False -> False with
      | True ->
        (Promotion (pawn_loc, (Loc (new_r, f)), Rook))::((Promotion
          (pawn_loc, (Loc (new_r, f)), Knight))::((Promotion (pawn_loc, (Loc
          (new_r, f)), Bishop))::((Promotion (pawn_loc, (Loc (new_r, f)),
          Queen))::[])))
      | False -> [])
   | False -> [])

(** val pawn_promotion_captures :
    squareLocation -> color -> position -> move list **)

let pawn_promotion_captures pawn_loc c = function
| Posn (pp, _, _, _) ->
  let Loc (r, f) = pawn_loc in
  (match indices_valid r f with
   | True ->
     let new_r = advance_pawn c r in
     let left_capture =
       match match leb (S O) f with
             | True -> occupied_by_enemy_piece new_r (sub f (S O)) pp c
             | False -> False with
       | True ->
         (PromotionWithCapture (pawn_loc, (Loc (new_r, (sub f (S O)))),
           Rook))::((PromotionWithCapture (pawn_loc, (Loc (new_r,
           (sub f (S O)))), Knight))::((PromotionWithCapture (pawn_loc, (Loc
           (new_r, (sub f (S O)))), Bishop))::((PromotionWithCapture
           (pawn_loc, (Loc (new_r, (sub f (S O)))), Queen))::[])))
       | False -> []
     in
     let right_capture =
       match occupied_by_enemy_piece new_r (add f (S O)) pp c with
       | True ->
         (PromotionWithCapture (pawn_loc, (Loc (new_r, (add f (S O)))),
           Rook))::((PromotionWithCapture (pawn_loc, (Loc (new_r,
           (add f (S O)))), Knight))::((PromotionWithCapture (pawn_loc, (Loc
           (new_r, (add f (S O)))), Bishop))::((PromotionWithCapture
           (pawn_loc, (Loc (new_r, (add f (S O)))), Queen))::[])))
       | False -> []
     in
     (match eqb new_r (final_rank_of_pawn c) with
      | True -> app left_capture right_capture
      | False -> [])
   | False -> [])

(** val pawn_moves : squareLocation -> color -> position -> move list **)

let pawn_moves pawn_loc c pos =
  app (pawn_forward_moves pawn_loc c pos)
    (app (pawn_captures pawn_loc c pos)
      (app (pawn_double_steps pawn_loc c pos)
        (app (en_passant_moves pawn_loc c pos)
          (app (pawn_forward_promotions pawn_loc c pos)
            (pawn_promotion_captures pawn_loc c pos)))))

(** val rook_moves : squareLocation -> color -> position -> move list **)

let rook_moves l c pos =
  app
    (append_forall (moves_to_square_on_rfd_list pos c l)
      (squares_on_same_rank l))
    (append_forall (moves_to_square_on_rfd_list pos c l)
      (squares_on_same_file l))

(** val bishop_moves : squareLocation -> color -> position -> move list **)

let bishop_moves l c pos =
  app
    (append_forall (moves_to_square_on_rfd_list pos c l)
      (squares_on_same_diagonal l))
    (append_forall (moves_to_square_on_rfd_list pos c l)
      (squares_on_same_antidiagonal l))

(** val knight_move_to_square :
    position -> color -> squareLocation -> squareLocation -> move option **)

let knight_move_to_square pos c fromL toL =
  let Posn (pp, _, _, _) = pos in
  (match is_square_empty toL pp with
   | True -> Some (FromTo (fromL, toL))
   | False ->
     (match is_square_occupied_by_enemy_piece toL pp c with
      | True -> Some (Capture (fromL, toL))
      | False -> None))

(** val knight_moves_to_squares :
    position -> color -> squareLocation -> squareLocation list -> move list **)

let rec knight_moves_to_squares pos c from = function
| [] -> []
| to0::rtos ->
  (match knight_move_to_square pos c from to0 with
   | Some move0 -> move0::(knight_moves_to_squares pos c from rtos)
   | None -> knight_moves_to_squares pos c from rtos)

(** val knight_moves : squareLocation -> color -> position -> move list **)

let knight_moves l c pos =
  let llu = VectorHV ((HStep (Left, (S (S O)))), (VStep (Up, (S O)))) in
  let lld = VectorHV ((HStep (Left, (S (S O)))), (VStep (Down, (S O)))) in
  let rru = VectorHV ((HStep (Right, (S (S O)))), (VStep (Up, (S O)))) in
  let rrd = VectorHV ((HStep (Right, (S (S O)))), (VStep (Down, (S O)))) in
  let uul = VectorHV ((HStep (Left, (S O))), (VStep (Up, (S (S O))))) in
  let uur = VectorHV ((HStep (Right, (S O))), (VStep (Up, (S (S O))))) in
  let ddl = VectorHV ((HStep (Left, (S O))), (VStep (Down, (S (S O))))) in
  let ddr = VectorHV ((HStep (Right, (S O))), (VStep (Down, (S (S O))))) in
  knight_moves_to_squares pos c l
    (target_squares l
      (llu::(lld::(rru::(rrd::(uul::(uur::(ddl::(ddr::[])))))))))

(** val queen_moves : squareLocation -> color -> position -> move list **)

let queen_moves l c pos =
  app (rook_moves l c pos) (bishop_moves l c pos)

(** val king_moves_to_empty_square :
    squareLocation -> color -> position -> move list **)

let king_moves_to_empty_square loc _ = function
| Posn (pp, _, _, _) ->
  map (fun to0 -> FromTo (loc, to0))
    (filter (fun sq -> is_square_empty sq pp) (adjacent_squares loc))

(** val king_captures : squareLocation -> color -> position -> move list **)

let king_captures loc c = function
| Posn (pp, _, _, _) ->
  map (fun to0 -> Capture (loc, to0))
    (filter (fun sq -> is_square_occupied_by_enemy_piece sq pp c)
      (adjacent_squares loc))

(** val king_moves : squareLocation -> color -> position -> move list **)

let king_moves loc c pos =
  app (king_moves_to_empty_square loc c pos) (king_captures loc c pos)

(** val moves_by_player_from_square :
    position -> color -> squareLocation -> move list **)

let moves_by_player_from_square pos c loc =
  let Posn (pp, _, _, _) = pos in
  let Loc (r, f) = loc in
  (match get_square_by_index pp r f with
   | Empty -> []
   | Occupied (sc, p) ->
     (match ceq c sc with
      | True ->
        (match p with
         | Pawn -> pawn_moves loc c pos
         | Rook -> rook_moves loc c pos
         | Knight -> knight_moves loc c pos
         | Bishop -> bishop_moves loc c pos
         | Queen -> queen_moves loc c pos
         | King -> king_moves loc c pos)
      | False -> []))

(** val moves_by_player : position -> color -> move list **)

let moves_by_player pos c =
  append_forall (fun sq -> moves_by_player_from_square pos c sq)
    valid_locations

(** val is_move_that_attacks_occupied_square :
    squareLocation -> move -> bool **)

let is_move_that_attacks_occupied_square loc move0 =
  match is_capturing_move move0 with
  | True -> locations_equal (toOfMove move0) loc
  | False -> False

(** val attacks_occupied_square :
    position -> color -> squareLocation -> bool **)

let attacks_occupied_square pos c loc =
  exists_in (moves_by_player pos c) (is_move_that_attacks_occupied_square loc)

(** val make_from_to_move_pp :
    piecePlacements -> squareLocation -> squareLocation -> piecePlacements **)

let make_from_to_move_pp before from to0 =
  let Loc (from_r, from_f) = from in
  let Loc (to_r, to_f) = to0 in
  let from_emptied = set_square_by_index before from_r from_f Empty in
  set_square_by_index from_emptied to_r to_f
    (get_square_by_index before from_r from_f)

(** val en_passant_capture_rank : color -> nat **)

let en_passant_capture_rank = function
| White -> S (S (S (S O)))
| Black -> S (S (S O))

(** val remove_en_passant_capture :
    piecePlacements -> squareLocation -> squareLocation -> piecePlacements **)

let remove_en_passant_capture pp from to0 =
  let Loc (from_r, _) = from in
  let Loc (_, to_f) = to0 in
  (match eqb from_r (en_passant_capture_rank White) with
   | True -> set_square_by_index pp (en_passant_capture_rank White) to_f Empty
   | False ->
     (match eqb from_r (en_passant_capture_rank Black) with
      | True ->
        set_square_by_index pp (en_passant_capture_rank Black) to_f Empty
      | False -> pp))

(** val make_en_passant_move_pp :
    piecePlacements -> squareLocation -> squareLocation -> piecePlacements **)

let make_en_passant_move_pp before from to0 =
  remove_en_passant_capture (make_from_to_move_pp before from to0) from to0

(** val promotion_rank : color -> nat **)

let promotion_rank = function
| White -> S (S (S (S (S (S (S O))))))
| Black -> O

(** val pp_from_map :
    (squareLocation -> square) -> squareLocation list -> piecePlacements ->
    piecePlacements **)

let rec pp_from_map f locs pp_acc =
  match locs with
  | [] -> pp_acc
  | s::rest ->
    let Loc (rnk, fl) = s in
    set_square_by_index (pp_from_map f rest pp_acc) rnk fl (f (Loc (rnk, fl)))

(** val make_promotion_move_map :
    piecePlacements -> squareLocation -> squareLocation -> color -> piece ->
    squareLocation -> square **)

let make_promotion_move_map before from to0 c piece0 loc =
  match locations_equal loc from with
  | True -> Empty
  | False ->
    (match locations_equal loc to0 with
     | True -> Occupied (c, piece0)
     | False -> get_square_by_location before loc)

(** val make_promotion_move_pp :
    piecePlacements -> squareLocation -> squareLocation -> piece ->
    piecePlacements **)

let make_promotion_move_pp before from to0 piece0 =
  match eqb (rank_of_loc to0) (promotion_rank White) with
  | True ->
    pp_from_map (make_promotion_move_map before from to0 White piece0)
      valid_locations empty_pp
  | False ->
    (match eqb (rank_of_loc to0) (promotion_rank Black) with
     | True ->
       pp_from_map (make_promotion_move_map before from to0 Black piece0)
         valid_locations empty_pp
     | False -> before)

(** val make_white_kingside_castling_move_map :
    piecePlacements -> squareLocation -> square **)

let make_white_kingside_castling_move_map before loc =
  match locations_equal loc (Loc (O, (S (S (S (S O)))))) with
  | True -> Empty
  | False ->
    (match locations_equal loc (Loc (O, (S (S (S (S (S (S O)))))))) with
     | True -> Occupied (White, King)
     | False ->
       (match locations_equal loc (Loc (O, (S (S (S (S (S (S (S O))))))))) with
        | True -> Empty
        | False ->
          (match locations_equal loc (Loc (O, (S (S (S (S (S O))))))) with
           | True -> Occupied (White, Rook)
           | False -> get_square_by_location before loc)))

(** val make_white_queenside_castling_move_map :
    piecePlacements -> squareLocation -> square **)

let make_white_queenside_castling_move_map before loc =
  match locations_equal loc (Loc (O, (S (S (S (S O)))))) with
  | True -> Empty
  | False ->
    (match locations_equal loc (Loc (O, (S (S O)))) with
     | True -> Occupied (White, King)
     | False ->
       (match locations_equal loc (Loc (O, O)) with
        | True -> Empty
        | False ->
          (match locations_equal loc (Loc (O, (S (S (S O))))) with
           | True -> Occupied (White, Rook)
           | False -> get_square_by_location before loc)))

(** val make_black_kingside_castling_move_map :
    piecePlacements -> squareLocation -> square **)

let make_black_kingside_castling_move_map before loc =
  match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S
          O)))))) with
  | True -> Empty
  | False ->
    (match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), (S (S (S
             (S (S (S O)))))))) with
     | True -> Occupied (Black, King)
     | False ->
       (match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), (S (S
                (S (S (S (S (S O))))))))) with
        | True -> Empty
        | False ->
          (match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), (S
                   (S (S (S (S O))))))) with
           | True -> Occupied (Black, Rook)
           | False -> get_square_by_location before loc)))

(** val make_black_queenside_castling_move_map :
    piecePlacements -> squareLocation -> square **)

let make_black_queenside_castling_move_map before loc =
  match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S
          O)))))) with
  | True -> Empty
  | False ->
    (match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), (S (S
             O)))) with
     | True -> Occupied (Black, King)
     | False ->
       (match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), O)) with
        | True -> Empty
        | False ->
          (match locations_equal loc (Loc ((S (S (S (S (S (S (S O))))))), (S
                   (S (S O))))) with
           | True -> Occupied (Black, Rook)
           | False -> get_square_by_location before loc)))

(** val make_castling_move_pp :
    piecePlacements -> color -> castlingType -> piecePlacements **)

let make_castling_move_pp before c ct =
  match ceq c White with
  | True ->
    (match ctypeeq ct KingSide with
     | True ->
       pp_from_map (make_white_kingside_castling_move_map before)
         valid_locations empty_pp
     | False ->
       pp_from_map (make_white_queenside_castling_move_map before)
         valid_locations empty_pp)
  | False ->
    (match ctypeeq ct KingSide with
     | True ->
       pp_from_map (make_black_kingside_castling_move_map before)
         valid_locations empty_pp
     | False ->
       pp_from_map (make_black_queenside_castling_move_map before)
         valid_locations empty_pp)

(** val initial_queenside_rook_location : color -> squareLocation **)

let initial_queenside_rook_location = function
| White -> Loc (O, O)
| Black -> Loc ((S (S (S (S (S (S (S O))))))), O)

(** val initial_kingside_rook_location : color -> squareLocation **)

let initial_kingside_rook_location = function
| White -> Loc (O, (S (S (S (S (S (S (S O))))))))
| Black -> Loc ((S (S (S (S (S (S (S O))))))), (S (S (S (S (S (S (S O))))))))

(** val initial_rook_location : castlingType -> color -> squareLocation **)

let initial_rook_location ctype c =
  match ctype with
  | QueenSide -> initial_queenside_rook_location c
  | KingSide -> initial_kingside_rook_location c

(** val remove_cavl :
    castlingAvailability -> castlingAvailability list -> castlingAvailability
    list **)

let remove_cavl cavl l =
  filter (fun c -> negb (cavleq c cavl)) l

(** val remove_cavls :
    color -> castlingAvailability list -> castlingAvailability list **)

let remove_cavls c l =
  filter (fun cavl -> let Cavl (_, cavl_c) = cavl in negb (ceq c cavl_c)) l

(** val is_initial_rook_move :
    castlingType -> piecePlacements -> castlingAvailability list -> move ->
    color -> bool **)

let is_initial_rook_move ctype pp cavl move0 c =
  match get_square_by_location pp (fromOfMove move0) with
  | Empty -> False
  | Occupied (square_c, piece0) ->
    (match match match eqPiece piece0 Rook with
                 | True ->
                   locations_equal (initial_rook_location ctype c)
                     (fromOfMove move0)
                 | False -> False with
           | True -> ceq square_c c
           | False -> False with
     | True -> exists_in cavl (fun cav -> cavleq cav (Cavl (ctype, c)))
     | False -> False)

(** val is_initial_queenside_rook_move :
    piecePlacements -> castlingAvailability list -> move -> color -> bool **)

let is_initial_queenside_rook_move pp cavl move0 c =
  is_initial_rook_move QueenSide pp cavl move0 c

(** val is_initial_kingside_rook_move :
    piecePlacements -> castlingAvailability list -> move -> color -> bool **)

let is_initial_kingside_rook_move pp cavl move0 c =
  is_initial_rook_move KingSide pp cavl move0 c

(** val make_from_to_move :
    position -> move -> piecePlacements -> color -> pawnDoubleStep option ->
    castlingAvailability list -> squareLocation -> squareLocation -> position **)

let make_from_to_move before move0 pp c _ cavl from to0 =
  match get_square_by_location pp from with
  | Empty -> before
  | Occupied (_, piece0) ->
    (match piece0 with
     | Rook ->
       (match is_initial_queenside_rook_move pp cavl move0 c with
        | True ->
          Posn ((make_from_to_move_pp pp from to0), (opponent_of c), None,
            (remove_cavl (Cavl (QueenSide, c)) cavl))
        | False ->
          (match is_initial_kingside_rook_move pp cavl move0 c with
           | True ->
             Posn ((make_from_to_move_pp pp from to0), (opponent_of c), None,
               (remove_cavl (Cavl (KingSide, c)) cavl))
           | False ->
             Posn ((make_from_to_move_pp pp from to0), (opponent_of c), None,
               cavl)))
     | King ->
       Posn ((make_from_to_move_pp pp from to0), (opponent_of c), None, [])
     | _ ->
       Posn ((make_from_to_move_pp pp from to0), (opponent_of c), None, cavl))

(** val make_move : position -> move -> position **)

let make_move before move0 =
  let Posn (pp, c, pds, cavl) = before in
  (match move0 with
   | FromTo (from, to0) ->
     make_from_to_move before move0 pp c pds cavl from to0
   | Capture (from, to0) ->
     make_from_to_move before move0 pp c pds cavl from to0
   | DoubleStep (from, to0) ->
     Posn ((make_from_to_move_pp pp from to0), (opponent_of c), (Some
       (DoubleStepRankFile ((rank_of_loc to0), (file_of_loc to0)))), cavl)
   | EnPassant (from, to0) ->
     Posn ((make_en_passant_move_pp pp from to0), (opponent_of c), None, cavl)
   | Promotion (from, to0, piece0) ->
     Posn ((make_promotion_move_pp pp from to0 piece0), (opponent_of c),
       None, cavl)
   | PromotionWithCapture (from, to0, piece0) ->
     Posn ((make_promotion_move_pp pp from to0 piece0), (opponent_of c),
       None, cavl)
   | Castle (castle_c, ctype) ->
     (match ceq castle_c c with
      | True ->
        Posn ((make_castling_move_pp pp c ctype), (opponent_of c), None,
          (remove_cavls c cavl))
      | False -> before))

(** val find_king : position -> color -> squareLocation list **)

let find_king pos c =
  find_piece pos c King valid_locations

(** val is_in_check : position -> color -> bool **)

let is_in_check pos c =
  exists_in (find_king pos c) (fun king_loc ->
    attacks_occupied_square pos (opponent_of c) king_loc)

(** val puts_king_in_check : position -> move -> bool **)

let puts_king_in_check pos move0 =
  is_in_check (make_move pos move0) (get_to_move pos)

(** val legal_moves : position -> move list **)

let legal_moves pos =
  filter (fun move0 -> negb (puts_king_in_check pos move0))
    (moves_by_player pos (get_to_move pos))

(** val is_checkmate : position -> bool **)

let is_checkmate pos =
  match is_in_check pos (get_to_move pos) with
  | True -> eqb O (length (legal_moves pos))
  | False -> False

type integer =
| PosInt of nat
| NegInt of nat

(** val intleq : integer -> integer -> bool **)

let intleq a b =
  match a with
  | PosInt p -> (match b with
                 | PosInt q -> leb p q
                 | NegInt _ -> False)
  | NegInt p -> (match b with
                 | PosInt _ -> True
                 | NegInt q -> leb q p)

(** val intadd : integer -> integer -> integer **)

let intadd a b =
  match a with
  | PosInt p ->
    (match b with
     | PosInt q -> PosInt (add p q)
     | NegInt q ->
       (match leb p q with
        | True -> NegInt (sub q p)
        | False -> PosInt (sub p q)))
  | NegInt p ->
    (match b with
     | PosInt q ->
       (match leb p q with
        | True -> PosInt (sub q p)
        | False -> NegInt (sub p q))
     | NegInt q -> NegInt (add p q))

(** val value_of_piece : piece -> nat **)

let value_of_piece = function
| Pawn -> S (S (S (S (S (S (S (S (S (S O)))))))))
| Rook ->
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))))))))))))))))))))
| Queen ->
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| King -> O
| _ ->
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S O)))))))))))))))))))))))))))))

(** val value_of_square : square -> color -> nat **)

let value_of_square sq c =
  match sq with
  | Empty -> O
  | Occupied (sc, p) ->
    (match ceq sc c with
     | True -> value_of_piece p
     | False -> O)

(** val value_of_material : piecePlacements -> color -> nat **)

let value_of_material pp c =
  let f = fun acc loc ->
    add acc (value_of_square (get_square_by_location pp loc) c)
  in
  fold_left f valid_locations O

(** val material_balance_of_position : piecePlacements -> integer **)

let material_balance_of_position pp =
  intadd (PosInt (value_of_material pp White)) (NegInt
    (value_of_material pp Black))

(** val value_for_player : nat -> color -> integer **)

let value_for_player v = function
| White -> PosInt v
| Black -> NegInt v

(** val evaluate_position : position -> integer **)

let evaluate_position pos =
  match is_checkmate pos with
  | True ->
    value_for_player (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (opponent_of (get_to_move pos))
  | False -> material_balance_of_position (get_piece_placements pos)

(** val find_optimal_element :
    'a1 list -> ('a1 -> 'a2) -> ('a2 -> 'a2 -> bool) -> 'a1 -> 'a2 -> 'a1 **)

let rec find_optimal_element l eval better best_element_so_far best_value_so_far =
  match l with
  | [] -> best_element_so_far
  | a::rest ->
    let new_value = eval a in
    (match better new_value best_value_so_far with
     | True -> find_optimal_element rest eval better a new_value
     | False ->
       find_optimal_element rest eval better best_element_so_far
         best_value_so_far)

type moveEvaluation =
| Eva of move * integer
| NoMoveEva of integer

(** val value_of_evaluation : moveEvaluation -> integer **)

let value_of_evaluation = function
| Eva (_, v) -> v
| NoMoveEva v -> v

(** val moves_worth_considering : position -> move list **)

let moves_worth_considering =
  legal_moves

(** val minimal_evaluation : moveEvaluation list -> moveEvaluation **)

let minimal_evaluation l = match l with
| [] -> NoMoveEva (PosInt O)
| h::_ ->
  find_optimal_element l value_of_evaluation intleq h (value_of_evaluation h)

(** val maximal_evaluation : moveEvaluation list -> moveEvaluation **)

let maximal_evaluation l = match l with
| [] -> NoMoveEva (PosInt O)
| h::_ ->
  find_optimal_element l value_of_evaluation (fun v1 v2 -> intleq v2 v1) h
    (value_of_evaluation h)

(** val evaluation_function_for_player :
    color -> moveEvaluation list -> moveEvaluation **)

let evaluation_function_for_player = function
| White -> maximal_evaluation
| Black -> minimal_evaluation

(** val evaluate_moves : nat -> position -> moveEvaluation list **)

let rec evaluate_moves depth pos =
  match depth with
  | O -> (NoMoveEva (evaluate_position pos))::[]
  | S d ->
    let player = get_to_move pos in
    let opponent = opponent_of player in
    let min_or_max = evaluation_function_for_player opponent in
    let evaluate_move = fun move0 -> Eva (move0,
      (value_of_evaluation
        (min_or_max (evaluate_moves d (make_move pos move0)))))
    in
    map evaluate_move (moves_worth_considering pos)

