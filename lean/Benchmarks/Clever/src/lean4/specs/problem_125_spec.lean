import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List (List Nat) → Nat → List Nat)
(grid: List (List Nat))
(k: Nat) :=
let lexographically_less (a b: List Nat) : Prop :=
  a.length = b.length ∧ a.length = k ∧
  (∃ i, i < k ∧ a.get! i < b.get! i ∧
  (∀ j, j < i → a.get! j = b.get! j));
let rec is_valid_path (k': Nat) (path: List Nat) (grid: List (List Nat)) : Prop :=
  let n := grid.length;
  path.length = k' →
  (∃ i j,
    (i < n ∧ j < n ∧ path.get! 0 = (grid.get! i).get! j) ∧
    (1 < path.length →
      ( ∃ i' j', i' < n ∧ j' < n ∧
        (path.get! 1 = (grid.get! i').get! j') ∧
        ((abs ((i: Int) - (i': Int)) = 1 ∧ j = j') ∨
         (abs ((j: Int) - (j': Int)) = 1 ∧ i = i'))) ∧
      (is_valid_path (k' - 1) (path.drop 1) grid))
  );
let spec (result: List Nat) :=
  let n := grid.length;
  (∀ i, i < n → (grid.get! i).length = n) →
  (∀ i j, i < n → j < n ↔ ((grid.get! i).get! j) ∈ [1, n^2]) →
  is_valid_path k result grid ∧ (∀ path, is_valid_path k path grid → lexographically_less result path);
∃ result, implementation grid k = result ∧
spec result

def implementation (grid: List (List Nat)) (k: Nat) : List Nat := sorry

theorem correctness
(grid: List (List Nat))
(k: Nat)
: problem_spec implementation grid k := sorry 