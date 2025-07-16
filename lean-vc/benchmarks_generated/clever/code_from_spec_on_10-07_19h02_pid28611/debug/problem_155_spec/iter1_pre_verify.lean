import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Int → Int × Int)
-- inputs
(num: Int) :=
-- spec
let spec (result: Int × Int) :=
  let (even_count, odd_count) := result;
  let numAbs := |num|.toNat;
  let numBy10 := numAbs/10;
  let (even_count', odd_count') := impl numBy10;
  (result = impl numAbs) ∧
  (0 ≤ num → (Even num ↔ 1 + even_count' = even_count) ∧ (Odd num ↔ even_count' = even_count)) ∧
  (0 ≤ num → (Odd num ↔ 1 + odd_count' = odd_count) ∧ (Even num ↔ odd_count' = odd_count));
-- program terminates
∃ result, impl num = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def count_even_odd_digits (n : Nat) : Nat × Nat :=
  if n = 0 then (1, 0)
  else
    let digit := n % 10
    let (even_rest, odd_rest) := count_even_odd_digits (n / 10)
    if digit % 2 = 0 then (even_rest + 1, odd_rest)
    else (even_rest, odd_rest + 1)

def implementation (num: Int) : Int × Int := 
  let n := |num|.toNat
  let (even_count, odd_count) := count_even_odd_digits n
  (even_count, odd_count)

-- LLM HELPER
lemma count_even_odd_digits_spec (n : Nat) :
  let (even_count, odd_count) := count_even_odd_digits n
  let (even_count', odd_count') := count_even_odd_digits (n / 10)
  (count_even_odd_digits n = (even_count, odd_count)) ∧
  (n = 0 → even_count = 1 ∧ odd_count = 0) ∧
  (n > 0 → 
    ((n % 10) % 2 = 0 → even_count = even_count' + 1 ∧ odd_count = odd_count') ∧
    ((n % 10) % 2 ≠ 0 → even_count = even_count' ∧ odd_count = odd_count' + 1)) := by
  simp [count_even_odd_digits]
  constructor
  · rfl
  constructor
  · intro h
    simp [h]
  · intro h
    simp [h]
    split_ifs with h1
    · constructor
      · intro h2
        simp [h2]
      · intro h2
        simp [h2]
    · constructor
      · intro h2
        simp [h2]
      · intro h2
        simp [h2]

-- LLM HELPER
lemma implementation_eq_count_even_odd_digits (num : Int) :
  implementation num = count_even_odd_digits |num|.toNat := by
  simp [implementation]

theorem correctness
(num: Int)
: problem_spec implementation num := by
  simp [problem_spec]
  use implementation num
  constructor
  · rfl
  · simp [implementation_eq_count_even_odd_digits]
    constructor
    · rfl
    constructor
    · intro h
      simp [Int.abs_nonneg] at h
      constructor
      · constructor
        · intro h_even
          simp [count_even_odd_digits_spec]
        · intro h_odd
          simp [count_even_odd_digits_spec]
      · constructor
        · intro h_odd
          simp [count_even_odd_digits_spec]
        · intro h_even
          simp [count_even_odd_digits_spec]
    · intro h
      simp [Int.abs_nonneg] at h
      constructor
      · constructor
        · intro h_odd
          simp [count_even_odd_digits_spec]
        · intro h_even
          simp [count_even_odd_digits_spec]
      · constructor
        · intro h_even
          simp [count_even_odd_digits_spec]
        · intro h_odd
          simp [count_even_odd_digits_spec]