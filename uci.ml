let log_file = "/home/andreas/chess/krr/log.txt";;
let log_oc = open_out log_file;;

Random.self_init ();;

let current_position = ref Engine.initial_position;;

let log str =
    Printf.fprintf log_oc "%s\n" str;;

let log_gui_command str =
    log (Printf.sprintf "GUI says: %s" str);;

let print_and_log str =
    print_endline str;
    log str;;

let rec int_of_nat n =
    match n with
    | Engine.O -> 0
    | S m -> 1 + (int_of_nat m);;
    
let rec nat_of_int i =
    match i with
    | 0 -> Engine.O
    | k -> S (nat_of_int (k - 1));;

let select_random_element l =
    let n = Random.int (List.length l) in
    List.nth l n;;

let string_of_fileindex findex =
    match (int_of_nat findex) with
    | 0 -> "a"
    | 1 -> "b"
    | 2 -> "c"
    | 3 -> "d"
    | 4 -> "e"
    | 5 -> "f"
    | 6 -> "g"
    | 7 -> "h"
    | _ -> "invalid file";;

let string_of_rankindex rindex =
    string_of_int ((int_of_nat rindex) + 1);;

let string_of_squareLocation sL =
    match sL with
    | Engine.Loc (rindex,findex) -> (string_of_fileindex findex)^(string_of_rankindex rindex);;

let letter_of_piece (p : Engine.piece) =
    match p with
    | Pawn -> "p"
    | Rook -> "r"
    | Knight -> "n"
    | Bishop -> "b"
    | Queen -> "q"
    | King -> "k";;

let piece_of_letter s =
    match s with
    | "p" -> Engine.Pawn
    | "r" -> Rook
    | "q" -> Queen
    | "n" -> Knight
    | "b" -> Bishop
    | "k" -> King
    | _ -> Pawn;;

let string_of_move (m : Engine.move) =
    match m with
    | FromTo (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | Capture (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | DoubleStep (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | EnPassant (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | Promotion (f, t, p) -> (string_of_squareLocation f) ^ (string_of_squareLocation t) ^ (letter_of_piece p)
    | PromotionWithCapture (f, t, p) -> (string_of_squareLocation f) ^ (string_of_squareLocation t) ^ (letter_of_piece p)
    | Castle (White, QueenSide) -> "e1c1"
    | Castle (White, KingSide) -> "e1g1"
    | Castle (Black, QueenSide) -> "e8c8"
    | Castle (Black, KingSide) -> "e8g8";;

let fileindex_of_string s =
    match s with
    | "a" -> nat_of_int 0
    | "b" -> nat_of_int 1
    | "c" -> nat_of_int 2
    | "d" -> nat_of_int 3
    | "e" -> nat_of_int 4
    | "f" -> nat_of_int 5
    | "g" -> nat_of_int 6
    | "h" -> nat_of_int 7
    | _ -> nat_of_int 7;;

let rankindex_of_string s =
    nat_of_int ((int_of_string s) - 1);;
    
let squareLocation_of_string s =
    Engine.Loc ((rankindex_of_string (String.sub s 0 1)),(fileindex_of_string (String.sub s 1 1)));;

let handle_uci str =
    if str = "uci" then (
        print_and_log "id name AH-Chess";
        print_and_log "id author Andreas Hofmeister";
        print_and_log "option name Difficulty type spin default 1 min 1 max 10";
        print_and_log "uciok";
        true
    )
    else
        false;;
    
let handle_isready str = 
    if str = "isready" then (
        print_and_log "readyok";
        true
    )
    else
        false;;
        
let movestring_list_of_string s =
    List.filter (fun x -> String.length x > 0) (List.map String.trim (String.split_on_char ' ' s));;
    
let is_on_final_rank (loc : Engine.squareLocation) (c : Engine.color) =
    let Engine.Loc (rank, _) = loc in
    match c with
    | White -> (int_of_nat rank = 7)
    | Black -> (int_of_nat rank = 0);;
    
let from_to_or_capture_move pp fromLoc toLoc =
    let toSq = Engine.get_square_by_location pp toLoc in
    match toSq with
    | Engine.Occupied (_,_) -> Engine.Capture (fromLoc, toLoc)
    | _ -> Engine.FromTo (fromLoc, toLoc);;
    
let is_en_passant_move toSq fromLoc toLoc =
    let Engine.Loc (_, fromFile) = fromLoc in
    let Engine.Loc (_, toFile) = toLoc in
    match toSq with
    | Engine.Occupied (_,_) -> false
    | _ -> fromFile <> toFile;;

let is_double_step fromLoc toLoc =
    let Engine.Loc (fromRank, _) = fromLoc in
    let Engine.Loc (toRank, _) = toLoc in
    abs((int_of_nat fromRank) - (int_of_nat toRank)) = 2;;

let move_of_movestring pos mstr =
    let Engine.Posn (pp, c, pds, cavl) = pos in
    let fromLoc = Engine.Loc (rankindex_of_string (String.sub mstr 1 1), fileindex_of_string (String.sub mstr 0 1)) in
    let toLoc = Engine.Loc (rankindex_of_string (String.sub mstr 3 1), fileindex_of_string (String.sub mstr 2 1)) in
    let toSq = Engine.get_square_by_location pp toLoc in
    let fromSq = Engine.get_square_by_location pp fromLoc in
    match fromSq with
    | Engine.Occupied (c, Engine.Pawn) -> 
        if is_on_final_rank toLoc c then begin
            let p = piece_of_letter (String.sub mstr 4 1) in
            match toSq with
            | Engine.Occupied (_,_) -> Engine.PromotionWithCapture (fromLoc, toLoc, p)
            | _ -> Engine.Promotion (fromLoc, toLoc, p)
        end else if is_en_passant_move toSq fromLoc toLoc then Engine.EnPassant (fromLoc, toLoc)
        else if is_double_step fromLoc toLoc then Engine.DoubleStep (fromLoc, toLoc)
        else from_to_or_capture_move pp fromLoc toLoc
    | Occupied (c, Engine.King) -> begin
        match mstr with
        | "e1c1" -> Engine.Castle (White, QueenSide)
        | "e1g1" -> Engine.Castle (White, KingSide)
        | "e8c8" -> Engine.Castle (Black, QueenSide)
        | "e8g8" -> Engine.Castle (Black, KingSide)
        | _ -> from_to_or_capture_move pp fromLoc toLoc
        end
    | _ -> from_to_or_capture_move pp fromLoc toLoc;;

let string_of_color_and_piece (c : Engine.color) p =
    match c with
    | White -> String.uppercase_ascii (letter_of_piece p)
    | Black -> letter_of_piece p;;

let string_of_square (sq : Engine.square) =
    match sq with
    | Occupied (c, p) -> string_of_color_and_piece c p
    | _ -> "_";;

let string_of_pp pp =
    let result = ref "" in
    let square = ref (Engine.Empty) in
    for rank = 7 downto 0 do
        for file = 0 to 6 do
            square := Engine.get_square_by_index pp (nat_of_int rank) (nat_of_int file);
            result := !result ^ (string_of_square !square)
        done;
        square := Engine.get_square_by_index pp (nat_of_int rank) (nat_of_int 7);
        result := !result ^ (string_of_square !square) ^ "\n";
    done;
    !result;;

let string_of_pos pos =
    let Engine.Posn (pp, c, pds, cavl) = pos in string_of_pp pp;;

let apply_movestring pos mstr =
    Engine.make_move pos (move_of_movestring pos mstr);;

let apply_movestrings pos mstrs =
    List.fold_left apply_movestring pos mstrs;;

let handle_position str =
    try (
        let words = List.filter (fun x -> String.length x > 0) (List.map String.trim (String.split_on_char ' ' str)) in
        if (List.nth words 0) <> "position" then false else
        if (List.nth words 1) <> "startpos" then false else
        if (List.nth words 2) <> "moves" then false else begin
            let movestrings = (List.tl (List.tl (List.tl words))) in
            current_position := apply_movestrings Engine.initial_position movestrings;
            log ("DEBUG, new position:\n"^(string_of_pos !current_position));
            true
        end
    )
    with
        | _ -> false;;

let int_of_eint engine_int =
    match engine_int with
    | (Engine.PosInt v) -> (int_of_nat v)
    | NegInt v -> -(int_of_nat v);;

let cmp_of_player c =
    match c with
    | Engine.White -> (fun ev1 ev2 -> 
        (int_of_eint (Engine.value_of_evaluation ev2)) - 
        (int_of_eint (Engine.value_of_evaluation ev1)))
    | Engine.Black -> (fun ev1 ev2 -> 
        (int_of_eint (Engine.value_of_evaluation ev1)) - 
        (int_of_eint (Engine.value_of_evaluation ev2)))

let rec moves_of_evaluations evs =
    match evs with
    | [] -> []
    | ev::tl -> match ev with
                | Engine.Eva (m,_) -> m::(moves_of_evaluations tl)
                | _ -> moves_of_evaluations tl;;

let string_of_evaluation ev =
    match ev with
    | Engine.Eva (m,v) -> (string_of_move m)^": "^(string_of_int (int_of_eint v))
    | Engine.NoMoveEva v -> "No move?: "^(string_of_int (int_of_eint v));;

let best_moves pos =
    let evaluations = Engine.evaluate_moves (nat_of_int 3) !current_position in
    let cmp = cmp_of_player (Engine.get_to_move pos) in
    let sorted_evaluations = List.sort cmp evaluations in
    let best_value = int_of_eint (Engine.value_of_evaluation (List.hd sorted_evaluations)) in
    let best_evaluations = List.filter (fun ev -> (int_of_eint (Engine.value_of_evaluation ev)) = best_value) sorted_evaluations in
    log "Sorted evaluations:";
    List.iter (fun ev -> log (string_of_evaluation ev)) sorted_evaluations;
    moves_of_evaluations best_evaluations;;

let handle_go str =
    let f wtime winc btime binc = () in
    try (
        Scanf.sscanf str "go wtime %d winc %d btime %d binc %d" f;
        let moves = best_moves !current_position in
        let move = select_random_element moves in
        print_and_log ("bestmove " ^ (string_of_move move));
        true
    )
    with
        | _ -> false;;

let handle_input input =
    if (handle_uci input) then ()
    else if (handle_isready input) then ()
    else if (handle_go input) then ()
    else if (handle_position input) then ()
    else ();;

let input_output_loop () =
    let finished = ref false in
    let input = ref "" in
    while !finished <> true do
        input := read_line ();
        log_gui_command !input;
        if !input = "quit" then
            finished := true
        else
            handle_input !input
    done;;

(*
List.iter (fun m -> Printf.printf "%s\n" (string_of_move m)) (Engine.legal_moves Engine.initial_position);;

print_endline (string_of_pos !current_position);;
*)

(*
let movestring = "g2g4 g7g6 b2b3 b8c6 a2a4 f8g7 c2c3 g7e5 d1c2 c6d4 c2d1 e5d6 c3d4 f7f6 h2h3 e7e5 a4a5 a7a6 h3h4 d8e7 d4e5 e8f8 e5d6 f8g7 d6e7 d7d5 g1h3 c8g4 h4h5 g8e7 b1a3 e7f5 h3f4 b7b6 a3c2 g7h6 h5g6 h6g7 c1a3 f5h4 a3c5 c7c6 c5a3 b6a5 h1h4 a8d8 f4d3 d8b8 h4h2 g4c8 a1b1 b8a8 c2e3 c8g4 b1c1 c6c5 h2h7 h8h7 d3f4 g4h5 g6h7 a8f8 e3d5 h5g6 d2d3 f8e8 c1c5 g6h7 d3d4 h7c2 d1c2 e8e3 f2e3";;

let movestrings = ref (List.filter (fun x -> String.length x > 0) (List.map String.trim (String.split_on_char ' ' movestring)));;

while List.length !movestrings > 0 do
    print_endline ("applying " ^ (List.hd !movestrings));
    current_position := apply_movestring !current_position (List.hd !movestrings);
    print_endline (string_of_pos !current_position);
    movestrings := List.tl !movestrings
done;;
*)
input_output_loop ();;

close_out log_oc;;
