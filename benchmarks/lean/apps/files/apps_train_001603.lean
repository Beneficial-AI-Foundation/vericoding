/-
# Task
 An `amazon` (also known as a queen+knight compound) is an imaginary chess piece that can move like a `queen` or a `knight` (or, equivalently, like a `rook`, `bishop`, or `knight`). The diagram below shows all squares which the amazon attacks from e4 (circles represent knight-like moves while crosses correspond to queen-like moves).

 ![](https://codefightsuserpics.s3.amazonaws.com/tasks/amazonCheckmate/img/amazon.png?_tm=1473934566013)

 Recently you've come across a diagram with only three pieces left on the board: a `white amazon`, `white king` and `black king`. 

 It's black's move. You don't have time to determine whether the game is over or not, but you'd like to figure it out in your head. 

 Unfortunately, the diagram is smudged and you can't see the position of the `black king`, so it looks like you'll have to check them all.

 Given the positions of white pieces on a standard chessboard, determine the number of possible black king's positions such that: 

* It's a checkmate (i.e. black's king is under amazon's 
 attack and it cannot make a valid move);

* It's a check (i.e. black's king is under amazon's attack 
 but it can reach a safe square in one move);

* It's a stalemate (i.e. black's king is on a safe square 
 but it cannot make a valid move);

* Black's king is on a safe square and it can make a valid move.

Note that two kings cannot be placed on two adjacent squares (including two diagonally adjacent ones).

# Example

 For `king = "d3" and amazon = "e4"`, the output should be `[5, 21, 0, 29]`.

 ![](https://codefightsuserpics.s3.amazonaws.com/tasks/amazonCheckmate/img/example1.png?_tm=1473934566299)

 `Red crosses` correspond to the `checkmate` positions, `orange pluses` refer to `checks` and `green circles` denote `safe squares`.

 For `king = "a1" and amazon = "g5"`, the output should be `[0, 29, 1, 29]`.

 ![](https://codefightsuserpics.s3.amazonaws.com/tasks/amazonCheckmate/img/example2.png?_tm=1473934566670)

 `Stalemate` position is marked by a `blue square`.

# Input

 - String `king`

Position of white's king in chess notation.

 - String `amazon`

Position of white's amazon in the same notation.

Constraints: `amazon ≠ king.`

# Output

An array of four integers, each equal to the number of black's king positions corresponding to a specific situation. The integers should be presented in the same order as the situations were described, `i.e. 0 for checkmates, 1 for checks, etc`.
-/

def ChessPos := String
def AmazonResult := List Int

-- <vc-helpers>
-- </vc-helpers>

def amazon_check_mate (king : ChessPos) (amazon : ChessPos) : AmazonResult :=
  sorry

theorem amazon_check_mate_list_len
  (king amazon : ChessPos)
  (h : king ≠ amazon) :
  (amazon_check_mate king amazon).length = 4 :=
  sorry

theorem amazon_check_mate_non_negative
  (king amazon : ChessPos)
  (h : king ≠ amazon)
  (i : Nat)
  (h2 : i < (amazon_check_mate king amazon).length) :
  (amazon_check_mate king amazon).get ⟨i, h2⟩ ≥ 0 :=
  sorry

theorem amazon_check_mate_sum_bound
  (king amazon : ChessPos)
  (h : king ≠ amazon) :
  (amazon_check_mate king amazon).foldl (·+·) 0 ≤ 62 :=
  sorry

theorem amazon_check_mate_bounds
  (king amazon : ChessPos)
  (h : king ≠ amazon) :
  let result := amazon_check_mate king amazon
  ∀ i : Nat, ∀ h2 : i < result.length,
    0 ≤ result.get ⟨i, h2⟩ ∧
    result.get ⟨i, h2⟩ ≤ 64 :=
  sorry

/-
info: [5, 21, 0, 29]
-/
-- #guard_msgs in
-- #eval amazon_check_mate "d3" "e4"

/-
info: [0, 29, 1, 29]
-/
-- #guard_msgs in
-- #eval amazon_check_mate "a1" "g5"

/-
info: [1, 32, 1, 23]
-/
-- #guard_msgs in
-- #eval amazon_check_mate "a3" "e4"

-- Apps difficulty: interview
-- Assurance level: unguarded