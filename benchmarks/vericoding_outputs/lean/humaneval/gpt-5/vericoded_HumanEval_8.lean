-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def implementation (numbers: List Int) : (Int × Int) :=
  match numbers with
  | [] => (0, 1)
  | x :: xs =>
    let (sum_tail, prod_tail) := implementation xs
    (sum_tail + x, x * prod_tail)
-- </vc-definitions>

-- <vc-theorems>
def problem_spec
-- function signature
(implementation: List Int → (Int × Int))
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: (Int × Int)) :=
let (sum, prod) := result;
(numbers = [] → sum = 0 ∧ prod = 1) ∧
(numbers ≠ [] →
(let (sum_tail, prod_tail) := implementation numbers.tail;
sum - sum_tail = numbers[0]! ∧
sum_tail * prod_tail + prod = sum * prod_tail));
-- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  refine ⟨implementation numbers, rfl, ?_⟩
  change
    let (sum, prod) := implementation numbers;
    (numbers = [] → sum = 0 ∧ prod = 1) ∧
    (numbers ≠ [] →
      (let (sum_tail, prod_tail) := implementation numbers.tail;
        sum - sum_tail = numbers[0]! ∧
        sum_tail * prod_tail + prod = sum * prod_tail))
  cases numbers with
  | nil =>
      simp [implementation]
  | cons x xs =>
      simp [implementation, List.tail, add_comm, add_mul]
-- </vc-theorems>

-- #test implementation [] = (0, 1)
-- #test implementation [1, 2, 3, 4] = (10, 24)