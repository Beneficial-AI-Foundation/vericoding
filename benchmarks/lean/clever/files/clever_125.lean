-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (grid: List (List Nat)) (k: Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(impl: List (List Nat) → Nat → List Nat)
-- inputs
(grid: List (List Nat))
(k: Nat) :=
-- spec
let lexographically_less (a b: List Nat) : Prop :=
  a.length = b.length ∧ a.length = k ∧
  (∃ i, i < k ∧ a[i]! < b[i]! ∧
  (∀ j, j < i → a[j]! = b[j]!));
let rec is_valid_path (k': Nat) (path: List Nat) (grid: List (List Nat)) : Prop :=
  let n := grid.length;
  path.length = k' →
  (∃ i j,
    (i < n ∧ j < n ∧ path[0]! = (grid[i]!)[j]!) ∧
    (1 < path.length →
      ( ∃ i' j', i' < n ∧ j' < n ∧
        (path[1]! = (grid[i']!)[j']!) ∧
        ((abs ((i: Int) - (i': Int)) = 1 ∧ j = j') ∨
         (abs ((j: Int) - (j': Int)) = 1 ∧ i = i'))) ∧
      (is_valid_path (k' - 1) (path.drop 1) grid))
  );
let spec (result: List Nat) :=
  let n := grid.length;
  (∀ i, i < n → (grid[i]!).length = n) →
  (∀ i j, i < n → j < n ↔ ((grid[i]!)[j]!) ∈ [1, n^2]) →
  is_valid_path k result grid ∧ (∀ path, is_valid_path k path grid → lexographically_less result path);
-- program terminates
∃ result, impl grid k = result ∧
-- return value satisfies spec
spec result

theorem correctness
(grid: List (List Nat))
(k: Nat)
: problem_spec implementation grid k := by
  sorry
-- </vc-theorems>