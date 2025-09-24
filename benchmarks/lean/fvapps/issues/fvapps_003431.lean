-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + List.sum xs

def List.modifyNth (xs : List α) (n : Nat) (v : α) : List α :=
  match n, xs with
  | _, [] => []
  | 0, x :: xs => v :: xs
  | n + 1, x :: xs => x :: modifyNth xs n v
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Nat.abs (n : Nat) : Nat := n

def socialist_distribution (population : List Nat) (minimum : Nat) : Option (List Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem socialist_distribution_properties {population : List Nat} {minimum : Nat}
  (h : population ≠ []) :
  match socialist_distribution population minimum with
  | none => minimum > List.sum population / List.length population
  | some result => 
      (List.length result = List.length population) ∧ 
      (List.sum result = List.sum population) ∧
      (∀ x ∈ result, x ≥ minimum) ∧
      (∀ x ∈ result, x ≥ 0) ∧
      (∀ i j, i < List.length result → j < List.length result → i ≠ j →
        let swapped := result.modifyNth i (result.get! j) |>.modifyNth j (result.get! i)
        (∀ x ∈ swapped, x ≥ minimum) →
        List.sum (List.zipWith (·-·) population result |>.map Nat.abs) ≤ 
        List.sum (List.zipWith (·-·) population swapped |>.map Nat.abs))
  := by sorry

theorem minimum_zero_returns_original {population : List Nat} (h : population ≠ []) :
  socialist_distribution population 0 = some population := by sorry

/-
info: [5, 5, 5, 15, 70]
-/
-- #guard_msgs in
-- #eval socialist_distribution [2, 3, 5, 15, 75] 5

/-
info: [5, 5, 5, 42, 43]
-/
-- #guard_msgs in
-- #eval socialist_distribution [2, 3, 5, 45, 45] 5

/-
info: [20, 20, 20, 20, 20]
-/
-- #guard_msgs in
-- #eval socialist_distribution [2, 3, 5, 15, 75] 20
-- </vc-theorems>