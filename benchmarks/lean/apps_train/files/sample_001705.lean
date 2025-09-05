table {
        width: 236px;
    }

    table, tr, td {
        border: 0px;
    }

In a grid of 4 by 4 squares you want to place a skyscraper in each square with only some clues:

The height of the skyscrapers is between 1 and 4
No two skyscrapers in a row or column may have the same number of floors
A clue is the number of skyscrapers that you can see in a row or column from the outside
Higher skyscrapers block the view of lower skyscrapers located behind them

Can you write a program that can solve this puzzle?

Example:

To understand how the puzzle works, this is an example of a row with 2 clues. Seen from the left side there are 4 buildings visible while seen from the right side only 1:

 4

 1

There is only one way in which the skyscrapers can be placed. From left-to-right all four buildings must be visible and no building may hide behind another building:

 4
 1
 2
 3
 4
 1

Example of a 4 by 4 puzzle with the solution:

 1
 2

 2

 1

 3

 1
 2

 2
 1
 4
 3

 3
 4
 1
 2
 2

 1
 4
 2
 3
 1

 1
 3
 2
 4

 3

Task:

Finish:

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
