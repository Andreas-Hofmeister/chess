import chess
import chess.engine
import sys

input_file = sys.argv[1]

def get_best_moves(fen_position, num_moves=5):
    engine_path = 'stockfish'  # Path to the Stockfish executable

    # Load the chess engine
    engine = chess.engine.SimpleEngine.popen_uci(engine_path)

    # Create a board from the FEN position
    board = chess.Board(fen_position)

    best_moves = []
    for _ in range(num_moves):
        try:
            # Perform the engine's best move calculation
            result = engine.play(board, chess.engine.Limit(time=10.0))  # Set a time limit for the engine's calculation

            # Get the best move
            best_move = result.move
            if not best_move:
                break
            best_moves.append(best_move)

            # Make the best move on the board
            board.push(best_move)
        except chess.engine.EngineError:
            # Handle engine errors (e.g., checkmate or stalemate)
            break
        except chess.engine.EngineTerminatedError:
            # Handle if the engine terminates unexpectedly
            break

    # Close the engine
    engine.quit()

    return best_moves
    
# Read FEN positions from a file
def read_fen_positions(file_path):
    with open(file_path, 'r') as file:
        fen_positions = file.readlines()
    return [fen.strip() for fen in fen_positions]

f = open("output.txt", "w")
positions = read_fen_positions(input_file)
for fen_position in positions:
    next_moves = get_best_moves(fen_position, num_moves=7)
    str_moves = map(str, next_moves)
    out_str = " ".join(str_moves)
    print(out_str)
    f.write(out_str+"\n")
f.close()
