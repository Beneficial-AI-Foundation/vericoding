There are n cards of different colours placed in a line, each of them can be either red, green or blue cards. Count the minimum number of cards to withdraw from the line so that no two adjacent cards have the same colour.

-----Input-----
- The first line of each input contains an integer n— the total number of cards.
- The next line of the input contains a string s, which represents the colours of the cards. We'll consider the cards in a line numbered from 1 to n from left to right. Then the $i^t$$^h$ alphabet equals "G", if the $i^t$$^h$ card is green, "R" if the card is red,  and "B", if it's blue.

-----Output-----
- Print a single integer — the answer to the problem.

-----Constraints-----
- $1 \leq n \leq 50$

-----Sample Input 1:-----
5
RGGBG

-----Sample Input 2:-----
5
RRRRR

-----Sample Input 3:-----
2
BB

-----Sample Output 1:-----
1

-----Sample Output 2:-----
4

-----Sample Output 3:-----
1

def count_min_cards_to_remove (n : Nat) (colors : List Color) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
