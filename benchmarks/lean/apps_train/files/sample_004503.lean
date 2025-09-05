Let's just place tokens on a connect four board.

** INPUT **

Provided as input the list of columns where a token is placed, from 0 to 6 included.
The first player starting is the yellow one (marked with `Y`), then the red (marked with `R`); the other cells might be empty and marked with `-`.

** OUTPUT **

The output is the state of the board after all the tokens in input have been placed.

** ASSUMPTIONS **

- The board is the standard 7x6;
- Of course you'll need to deal with gravity;
- You don't need to hassle with wrong input, wrong column numbers, checking for full column or going off the board;
- the columns list will always include proper column numbers;
- Notice: when you read the results in tests, the highest row appears first and the lowest row appears last; debugging using `\n` after each row might help (check example);

** EXAMPLES **

1.
```
Moves = [0,1,2,5,6]

Result:
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['Y', 'R', 'Y', '-', '-', 'R', 'Y']
```
2.
```
Moves = [0,1,2,5,6,2,0,0]

Result:
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['-', '-', '-', '-', '-', '-', '-']
['R', '-', '-', '-', '-', '-', '-']
['Y', '-', 'R', '-', '-', '-', '-']
['Y', 'R', 'Y', '-', '-', 'R', 'Y']
```

See test cases for better details.

def Board := List (List Cell)

def connect_four_place (moves: List Nat) : Board :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded