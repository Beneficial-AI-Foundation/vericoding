import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=

-- spec
let spec (result: Int) :=
  let dig_sum (x: Int): Int :=
    let digs := x.natAbs.digits 10;
    if x >= 0 then
      (List.map (fun t => (t: Int)) digs).sum
    else
      (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int);
  (arr = [] → result = 0) ∧
  (arr ≠ [] → 0 < (dig_sum arr[0]!) → result = 1 + implementation (arr.drop 1)) ∧
  (arr ≠ [] → (dig_sum arr[0]!) ≤ 0 → result = implementation (arr.drop 1));
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
def dig_sum (x: Int): Int :=
  let digs := x.natAbs.digits 10;
  if x >= 0 then
    (List.map (fun t => (t: Int)) digs).sum
  else
    (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int)

def implementation (arr: List Int) : Int :=
  match arr with
  | [] => 0
  | h :: t => 
    if 0 < dig_sum h then
      1 + implementation t
    else
      implementation t

-- LLM HELPER
theorem dig_sum_unfold (x: Int) : 
  dig_sum x = 
    let digs := x.natAbs.digits 10;
    if x >= 0 then
      (List.map (fun t => (t: Int)) digs).sum
    else
      (List.map (fun t => (t: Int)) (digs.drop 1)).sum - (digs[0]! : Int) :=
by rfl

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= by
  induction arr with
  | nil =>
    simp [problem_spec]
    use 0
    simp [implementation]
    constructor
    · intro h
      rfl
    constructor
    · intro h
      exfalso
      exact h rfl
    · intro h
      exfalso
      exact h rfl
  | cons h t ih =>
    simp [problem_spec]
    cases' ih with result ih_spec
    cases' ih_spec with ih_eq ih_props
    by_cases hpos : 0 < dig_sum h
    · simp [implementation, hpos]
      use 1 + result
      simp [dig_sum_unfold]
      constructor
      · rw [ih_eq]
      · constructor
        · intro h_eq
          injection h_eq
        constructor
        · intro h_ne
          simp [hpos]
          rw [ih_eq]
        · intro h_ne h_nonpos
          exfalso
          exact not_lt.mpr h_nonpos hpos
    · simp [implementation, hpos]
      use result
      simp [dig_sum_unfold]
      constructor
      · rw [ih_eq]
      · constructor
        · intro h_eq
          injection h_eq
        constructor
        · intro h_ne h_pos
          exfalso
          exact hpos h_pos
        · intro h_ne h_nonpos
          rw [ih_eq]