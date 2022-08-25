let log_file = "/home/andreas/chess/krr/log.txt";;
let log_oc = open_out log_file;;

let log str =
    Printf.fprintf log_oc "%s\n" str;;

let log_gui_command str =
    log (Printf.sprintf "GUI says: %s" str);;

let print_and_log str =
    print_endline str;
    log str;;
    
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
        
let handle_go str =
    let f wtime winc btime binc = () in
    try (
        Scanf.sscanf str "go wtime %d winc %d btime %d binc %d" f;
        print_and_log "bestmove c7c5";
        true
    )
    with
        | _ -> false;;

let handle_input input =
    if (handle_uci input) then ()
    else if (handle_isready input) then ()
    else if (handle_go input) then ()
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

input_output_loop ();;

close_out log_oc;;
