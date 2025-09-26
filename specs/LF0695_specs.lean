-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs

inductive Perm {α : Type} : List α → List α → Prop where
  | nil : Perm [] []
  | cons : ∀ (x : α) (l₁ l₂ : List α), Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
  | swap : ∀ (x y : α) (l : List α), Perm (x::y::l) (y::x::l)
  | trans : ∀ {l₁ l₂ l₃ : List α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_min_operations (n : Nat) (candies : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_box_zero_ops {val : Nat} :
  calc_min_operations 1 [val] = 0 :=
sorry

theorem min_ops_nonnegative {n : Nat} (candies : List Nat) :
  calc_min_operations n candies ≥ 0 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval calc_min_operations 4 [7, 8, 6, 4]

/-
info: 10
-/
-- #guard_msgs in
-- #eval calc_min_operations 6 [7, 3, 10, 2, 3, 8]

/-
info: 0
-/
-- #guard_msgs in
-- #eval calc_min_operations 1 [10]
-- </vc-theorems>