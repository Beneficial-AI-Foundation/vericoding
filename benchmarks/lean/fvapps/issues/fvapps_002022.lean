-- <vc-preamble>
def CumTree.vstavi : CumTree → Int → Unit := sorry
def CumTree.manjsi : CumTree → Int → Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_game : Nat → List Int → Int := sorry

inductive Sorted {α : Type} (r : α → α → Prop) : List α → Prop
  | nil : Sorted r []
  | single : (a : α) → Sorted r [a]
  | cons : (a b : α) → (l : List α) → r a b → Sorted r (b::l) → Sorted r (a::b::l)
-- </vc-definitions>

-- <vc-theorems>
theorem cumtree_single_value (val : Int) 
  (h1 : 1 ≤ val) (h2 : val ≤ 4096) :
  let ct := CumTree.mk 1 4096;
  ct.manjsi val = 0 ∧ 
  ct.manjsi (val + 1) = 1 ∧
  ct.manjsi (val - 1) = 0 := sorry

theorem solve_game_basic_properties {n : Nat} {nums : List Int}
  (h1 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 4096)
  (h2 : nums.length = n)
  (h3 : nums.Nodup) :
  solve_game n nums ≥ 0 ∧ 
  ∃ k : Int, solve_game n nums = k := sorry

theorem solve_game_sorted_zero {n : Nat} {nums : List Int}
  (h1 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 4096)
  (h2 : nums.length = n)
  (h3 : nums.Nodup)
  (h4 : Sorted (· < ·) nums) : 
  solve_game n nums = 0 := sorry

theorem solve_game_two_elements {a b : Int}
  (h1 : 1 ≤ a ∧ a ≤ 4096)
  (h2 : 1 ≤ b ∧ b ≤ 4096)
  (h3 : a ≠ b) :
  solve_game 2 [a, b] = if a > b then 1 else 0 := sorry
-- </vc-theorems>