Every character in the string “IITMANDI” is given a certain number of points. You are given a scrabble board with only one row. The input contains the positions of score modifiers such as: Double Letter, Triple Letter, Double Word and Triple Word. You need to find the best position to place the string “IITMANDI” such that your score is maximized. 
Double Letter - Doubles the number of points you get for the letter placed on the double letter.
Triple Letter - Triples the number of points you get for the letter placed on the triple letter.
Double Word - Doubles the number of points you get for the word. Applied after applying above modifiers.
Triple Word - Triples the number of points you get for the word. Applied after applying the above modifiers.
The word has to be read from left to right. You can’t place it in the reverse direction.

The letters have to be placed continuously on the board.

If there is no modifier or a double word or triple word modifier before a tile, it's score is added to the total score. The double word and triple modifiers are applied at the end.

-----Input Format-----
- First line containes a single integer $T$ - the number of test cases.
- First line of each test case contains a single integer $N$ - the size of the board.    
- Second line of each test case contains a string of size $N$ representing the board according to the following convention:

'.' - No modifier

'd' - Double letter

't' - Triple letter

'D' - Double word

'T' - Triple word     
- Third line of each test case contains 8 integers corresponding to the points associated with each letter of the string "IITMANDI". Note that the 3 'I's in IITMANDI cannot be interchanged freely. The score of the first 'I' will be equal to the first integer, score of the second 'I' will be equal to the second integer and the score of the last 'I' will be equal to the last integer.

-----Output Format-----
For each test case, output a single integer in a new line, the maximum possible score. 

-----Constraints-----
$ 1 \leq T \leq 1000 $
$ 8 \leq N \leq 100 $
$ 0 \leq $ Points for each character $ \leq 10^5 $ 

-----Sample Input-----
2

10

..d.t.D..d

10 11 12 9 8 10 11 15

22

dtDtTD..ddT.TtTdDT..TD

12297 5077 28888 17998 12125 27400 31219 21536

-----Sample Output-----
270

35629632

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded