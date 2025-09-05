A chess position can be expressed as a string using the  Forsyth–Edwards Notation (FEN). Your task is to write a parser that reads in a FEN-encoded string and returns a depiction of the board using the Unicode chess symbols (♔,♕,♘,etc.). The board should be drawn from the perspective of the active color (i.e. the side making the next move). 

Using the CodeWars dark theme is strongly recommended for this kata. Otherwise, the colors will appear to be inverted.

The complete FEN format contains 6 fields separated by spaces, but we will only consider the first two fields: Piece placement and active color (side-to-move). The rules for these fields are as follows:

The first field of the FEN describes piece placement.
Each row ('rank') of the board is described one-by-one, starting with rank 8 (the far side of the board from White's perspective) and ending with rank 1 (White's home rank). Rows are separated by a forward slash ('/').
Within each row, the contents of the squares are listed starting with the "a-file" (White's left) and ending with the "h-file" (White's right).
Each piece is identified by a single letter: pawn = P, knight = N, bishop = B, rook = R, queen = Q and king = K. White pieces are upper-case (PNBRQK), while black pieces are lowercase (pnbrqk).
Empty squares are represented using the digits 1 through 8 to denote the number of consecutive empty squares.
The piece placement field is followed by a single space, then a single character representing the color who has the next move ('w' for White and 'b' for Black).
Four additional fields follow the active color, separated by spaces. These fields can be ignored.

Using this encoding, the starting position is:

```rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1```

Using the characters "＿" and "▇" to represent dark and light unoccupied spaces, respectively, the starting position using the Unicode pieces would be:

♖♘♗♕♔♗♘♖
♙♙♙♙♙♙♙♙
▇＿▇＿▇＿▇＿
＿▇＿▇＿▇＿▇
▇＿▇＿▇＿▇＿
＿▇＿▇＿▇＿▇
♟♟♟♟♟♟♟♟
♜♞♝♛♚♝♞♜

After the move 1. Nf3, the FEN would be...

```rnbqkbnr/pppppppp/8/8/8/5N2/PPPPPPPP/RNBQKB1R b KQkq - 1 1```

...and because we draw the board from the perspective of the active color, the Unicode board would be:

♜＿♝♛♚♝♞♜
♟♟♟♟♟♟♟♟
▇＿♞＿▇＿▇＿
＿▇＿▇＿▇＿▇
▇＿▇＿▇＿▇＿
＿▇＿▇＿▇＿▇
♙♙♙♙♙♙♙♙
♖♘♗♕♔♗♘♖

Symbols

*Again, note that these colors are inverted from the Unicode character names because most people seem to use the dark theme for CodeWars.

Empty white square: ▇ (2587)
Empty black square: ＿ (FF3F)
White king (K): ♚ (265A)
White queen (Q): ♛ (265B)
White rook (R): ♜ (265C)
White bishop (B): ♝ (265D)
White knight (N): ♞ (265E)
White pawn (P): ♟ (265F)
Black king (k): ♔ (2654)
Black queen (q): ♕ (2655)
Black rook (r): ♖ (2656)
Black bishop (b): ♗ (2657)
Black knight (n): ♘ (2658)
Black pawn (p): ♙ (2659)

NB: Empty squares must have the proper colors. The bottom-right and top-left squares on a chess board are white.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
