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

let string_of_move (m : Engine.move) =
    match m with
    | FromTo (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | Capture (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | DoubleStep (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | EnPassant (f, t) -> (string_of_squareLocation f) ^ (string_of_squareLocation t)
    | Promotion (_, _, _) -> "Todo"
    | PromotionWithCapture (_, _, _) -> "Todo"
    | Castle (_, _) -> "Todo";;

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
    
let move_of_movestring pos mstr =
    let Engine.Posn (pp, c, pds, cavl) = pos in
    let fromLoc = Engine.Loc (rankindex_of_string (String.sub mstr 1 1), fileindex_of_string (String.sub mstr 0 1)) in
    let toLoc = Engine.Loc (rankindex_of_string (String.sub mstr 3 1), fileindex_of_string (String.sub mstr 2 1)) in
    let toSq = Engine.get_square_by_location pp toLoc in
    match toSq with
    | Engine.Occupied (_,_) -> Engine.Capture (fromLoc, toLoc)
    | _ -> Engine.FromTo (fromLoc, toLoc);;
        

let letter_of_piece (p : Engine.piece) =
    match p with
    | Pawn -> "p"
    | Rook -> "r"
    | Knight -> "n"
    | Bishop -> "b"
    | Queen -> "q"
    | King -> "k";;

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
(*
let movestrings = Scanf.sscanf "position startpos moves e2e4 f7f5 e4f5 d7d6 d1h5" "position startpos moves %s" movestring_list_of_string;;

print_endline (String.concat " " movestrings);;

current_position := apply_movestrings Engine.initial_position movestrings;;

print_endline (string_of_pos !current_position);;
*)

input_output_loop ();;

close_out log_oc;;
