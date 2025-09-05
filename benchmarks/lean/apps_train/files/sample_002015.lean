Fox Ciel is playing a card game with her friend Fox Jiro. There are n piles of cards on the table. And there is a positive integer on each card.

The players take turns and Ciel takes the first turn. In Ciel's turn she takes a card from the top of any non-empty pile, and in Jiro's turn he takes a card from the bottom of any non-empty pile. Each player wants to maximize the total sum of the cards he took. The game ends when all piles become empty.

Suppose Ciel and Jiro play optimally, what is the score of the game?

-----Input-----

The first line contain an integer n (1 ≤ n ≤ 100). Each of the next n lines contains a description of the pile: the first integer in the line is s_{i} (1 ≤ s_{i} ≤ 100) — the number of cards in the i-th pile; then follow s_{i} positive integers c_1, c_2, ..., c_{k}, ..., c_{s}_{i} (1 ≤ c_{k} ≤ 1000) — the sequence of the numbers on the cards listed from top of the current pile to bottom of the pile.

-----Output-----

Print two integers: the sum of Ciel's cards and the sum of Jiro's cards if they play optimally.

-----Examples-----
Input
2
1 100
2 1 10

Output
101 10

Input
1
9 2 8 6 5 9 4 7 1 3

Output
30 15

Input
3
3 1 3 2
3 5 4 6
2 8 7

Output
18 18

Input
3
3 1000 1000 1000
6 1000 1000 1000 1000 1000 1000
5 1000 1000 1000 1000 1000

Output
7000 7000

-----Note-----

In the first example, Ciel will take the cards with number 100 and 1, Jiro will take the card with number 10.

In the second example, Ciel will take cards with numbers 2, 8, 6, 5, 9 and Jiro will take cards with numbers 4, 7, 1, 3.

def Card := Nat 
def Pile := List Card

def Game := List (Nat × Pile)

def listSum (l : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
