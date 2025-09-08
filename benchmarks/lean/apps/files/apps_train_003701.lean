/-
Jack and Jill are playing a game. They have balls numbered from `0` to `n - 1`. Jack looks the other way and asks Jill to reverse the position of the balls, for instance, to change the order from say, `0,1,2,3` to `3,2,1,0`. He further asks Jill to reverse the position of the balls `n` times, each time starting from one position further to the right, till she reaches the last ball. So, Jill has to reverse the positions of the ball starting from position `0`, then from position `1`, then from position `2` and so on. At the end of the game, Jill will ask Jack to guess the final position of any ball numbered `k`. 

You will be given `2` integers, the first will be `n`(balls numbered from `0` to `n-1`) and the second will be `k`. You will return the position of the ball numbered `k` after the rearrangement.

```Perl
solve(4,1) = 3. The reversals are [0,1,2,3] -> [3,2,1,0] -> [3,0,1,2] -> [3,0,2,1]. => 1 is in position 3.
```

More examples in the test cases. Good luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def solve (count ball : Nat) : Nat :=
  sorry

theorem solve_in_range (count : Nat) (ball : Nat) (h : count > 0) : 
  solve count ball % count < count := by
  sorry

theorem solve_uniqueness (count : Nat) (h : count > 0) :
  ∀ b₁ b₂ : Nat, b₁ < count → b₂ < count → b₁ ≠ b₂ → solve count b₁ ≠ solve count b₂ := by
  sorry

theorem solve_deterministic (count ball : Nat) (h : count > 0) :
  solve count ball = solve count ball := by
  sorry

theorem solve_exists_output (count : Nat) (h : count > 0) :
  ∃ res : Nat, res = solve count 0 ∧ res < count := by
  sorry

theorem solve_specific_examples :
  solve 4 1 = 3 ∧ 
  solve 4 2 = 2 ∧
  solve 20 8 = 17 := by
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve 4 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 4 2

/-
info: 17
-/
-- #guard_msgs in
-- #eval solve 20 8

-- Apps difficulty: introductory
-- Assurance level: guarded