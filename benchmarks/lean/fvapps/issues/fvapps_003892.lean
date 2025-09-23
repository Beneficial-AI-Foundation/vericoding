-- <vc-preamble>
def max_tri_sum (nums : List Int) : Int := 
sorry

def List.sort (lt : α → α → Bool) : List α → List α :=
sorry

def List.sum : List Int → Int :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.dedup : List α → List α :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_tri_sum_perm_invariant {nums₁ nums₂ : List Int} 
  (h₁ : nums₁.length ≥ 3)
  (h₂ : nums₂.length ≥ 3)
  (h_perm : List.Perm nums₁ nums₂) : 
  max_tri_sum nums₁ = max_tri_sum nums₂ := sorry

/-
info: 17
-/
-- #guard_msgs in
-- #eval max_tri_sum [3, 2, 6, 8, 2, 3]

/-
info: -9
-/
-- #guard_msgs in
-- #eval max_tri_sum [-3, -27, -4, -2, -27, -2]

/-
info: 41
-/
-- #guard_msgs in
-- #eval max_tri_sum [-7, 12, -7, 29, -5, 0, -7, 0, 0, 29]
-- </vc-theorems>