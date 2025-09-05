Indian National Olympiad in Informatics 2013
Calvin wakes up early one morning and finds that all his friends in the hostel are asleep. To amuse himself, he decides to play the following game : he draws a sequence of N squares on the ground, numbered 1 to N, and writes an integer in each square. He starts at square k (1 ≤ k ≤ N). The game consists of one forward phase followed by one backward phase.
- In the forward phase, Calvin makes zero or more moves of the following type : if his current position is p, he can jump to p+1 or p+2 as long as he stays within the N squares.
- In the backward phase, Calvin makes zero or more moves of the following type : if his current position is p, he can jump to p−1 or p−2 as long as he stays within the N squares.
He plays such that he finally ends up at square 1, and then he stops. He starts with a score of 0, and each time he jumps from square i to square j, he adds the integer written in square j to his score. Find the maximum score Calvin can obtain by playing this game. Recall that Calvin must start at square k and end at square 1. The integer on the square where he starts is not included in his score.
For example, suppose N = 5 and the numbers in squares are 5, 3, −2, 1, 1. If k = 2, Calvin starts on the second square. He can make a forward move to square 4, another to square 5, a backward move to square 4, another to square 2, and another to square 1. His total score is 1+1+1+3+5 = 11. You can check that this is the maximum score possible.

-----Input format-----
• Line 1 : Two space-separated integers, N and k, with 1 ≤ k ≤ N.
• Line 2 : A space-separated sequence of N integers, the numbers in squares 1, 2 . . . , N .

-----Output format-----
A single line with a single integer, the maximum score Calvin can obtain by playing the game.

-----Test Data-----
The testdata is grouped into two subtasks with the following constraints on the inputs.
• Subtask 1 [30 points] : 1 ≤ N ≤ 3000.
• Subtask 2 [70 points] : 1 ≤ N ≤ 106.
In all subtasks, the number in each square is between −1000 and 1000 inclusive.

-----Example-----
Here is the sample input and output corresponding to the example above.

-----Sample input-----
5 2
5 3 -2 1 1

-----Sample output-----
11

Note: Your program should not print anything other than what is specified in the output format. Please remove all diagnostic print statements before making your final submission. A program with extraneous output will be treated as incorrect!

def find_max_score (N : Nat) (K : Nat) (A : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded