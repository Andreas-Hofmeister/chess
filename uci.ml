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
    
let is_en_passant_move fromLoc toLoc =
    let Engine.Loc (_, fromFile) = fromLoc in
    let Engine.Loc (_, toFile) = toLoc in
    fromFile <> toFile;;

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
        end else if is_en_passant_move fromLoc toLoc then Engine.EnPassant (fromLoc, toLoc)
        else if is_double_step fromLoc toLoc then Engine.DoubleStep (fromLoc, toLoc)
        else from_to_or_capture_move pp fromLoc toLoc
    | Occupied (c, Engine.King) -> begin
        match mstr with
        | "e1c1" -> Engine.Castle (White, QueenSide)
        | "e1g1" -> Engine.Castle (White, KingSide)
        | "e8c1" -> Engine.Castle (Black, QueenSide)
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
        if (List.nth words 2) <> "moves" then false else
        let movestrings = (List.tl (List.tl (List.tl words))) in
        current_position := apply_movestrings Engine.initial_position movestrings;
        log ("DEBUG, new position:\n"^(string_of_pos !current_position));
        true
    )
    with
        | _ -> false;;
        
let handle_go str =
    let f wtime winc btime binc = () in
    try (
        Scanf.sscanf str "go wtime %d winc %d btime %d binc %d" f;
        let moves = (Engine.legal_moves !current_position) in
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
let movestring = "e2e4 d7d5 e4d5 h7h5 d1h5 c7c5 h5h8 d8c7 h8g8 e8d8 g8f8 d8d7 f8f7 c7e5 e1d1 b7b5 f7e7 d7e7 d2d3 e5f4 c1f4 c8e6 f4b8 e7d8 d3d4 e6g8 f1b5 g7g6 g1f3 a8b8 b1c3 g6g5 f3g5 g8h7 g5h7 d8c7 d5d6 c7d8 b5d7 a7a5 c3d5 b8c8 d5f6 c5d4 h7f8 c8c4 b2b3 c4c5 b3b4 c5b5 c2c4 a5b4 c4b5 d4d3 b5b6 d3d2 b6b7";;

let movestrings = List.filter (fun x -> String.length x > 0) (List.map String.trim (String.split_on_char ' ' movestring));;

current_position := apply_movestrings Engine.initial_position movestrings;;

print_endline (string_of_pos !current_position);;

let moves = (Engine.legal_moves !current_position);;

List.iter (fun m -> Printf.printf "%s\n" (string_of_move m)) (moves);;

input_output_loop ();;

close_out log_oc;;
