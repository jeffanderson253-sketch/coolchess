# Cool Chess 1.3

Cool Chess is a small, self-contained chess program and engine written in QB64 BASIC. It is meant to be a playable hobby engine rather than a tournament-strength project: open the program, play on the graphical board, and let the engine reply.

## What it does

* Play by clicking squares or by entering coordinate moves such as `e2e4`, `e2-e4`, `o-o`, or `e7e8q`.
* Handles castling, en passant, promotion, checkmate, stalemate, threefold repetition, the fifty-move rule, and common insufficient-material draws.
* Shows legal-move markers, move history in SAN, captured pieces, last-move highlights, check status, and a flippable board.
* Supports talebacks, FEN display, PGN export, hints, engine-vs-human play, adjustable search depth, and per-move time limits.
* Uses iterative-deepening negamax with alpha-beta pruning, quiescence search, check extensions, MVV-LVA ordering, killer moves, Zobrist hashing, and a transposition table.

The project has no external graphics files: the board UI and piece sprites are contained in the BASIC source.

## Running it

### Windows executable

Download the executable from this repository's Releases page and run it normally. The program writes a PGN named `coolchess.pgn` beside the program when you use the `pgn` command.

### Build from source

Open `COOLCHESS13.bas` in a current QB64-PE installation, then run or build it from the IDE. The project is a single BASIC source file, so there are no additional assets or dependencies to install.

## A note about the EXE and antivirus warnings

The Windows EXE distributed with this project is **not a virus**. It is an unsigned executable compiled from the source in this repository by a hobbyist GitHub build workflow. New, unsigned binaries have no publisher reputation, so Windows SmartScreen or an antivirus product may show a warning even when the file is benign.

The complete QB64 source is included here so you can inspect it or build the executable yourself. As with any download, only use releases obtained from this repository; do not bypass a security warning for a file obtained from an unrelated site or re-upload.

## Commands

| Command                      | What it does                                                |
| ---------------------------- | ----------------------------------------------------------- |
| `new`                        | Start a new game as White.                                  |
| `undo` / `back`              | Take back two plies when possible.                          |
| `redo`                       | Replay plies removed by the last takeback.                  |
| `flip`                       | Put the other side at the bottom of the board.              |
| `go`                         | Let the engine play the side to move.                       |
| `hint`                       | Search for a move without playing it.                       |
| `depth 1` through `depth 10` | Set the maximum search depth.                               |
| `time n`                     | Set a per-move time limit in seconds; `time 0` disables it. |
| `eval`                       | Show the static evaluation in centipawns.                   |
| `fen`                        | Show the current FEN in the message panel.                  |
| `pgn`                        | Export the current game to `coolchess.pgn`.                 |
| `help`                       | Show the in-program command reference.                      |
| `quit`                       | Exit the program.                                           |

During a search, press `SPACE` to use the last completed iteration or `ESC` to cancel the search without changing the position.

## Status

This is a hobby project and a good target for experimentation. Feedback on move generation, search behavior, evaluation, QB64 compatibility, and UI details is welcome.
