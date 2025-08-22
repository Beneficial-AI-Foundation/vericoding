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
  (Int.ofNat even_count, Int.ofNat odd_count)

-- LLM HELPER
lemma count_even_odd_digits_base (n : Nat) :
  n = 0 → count_even_odd_digits n = (1, 0) := by
  intro h
  simp [count_even_odd_digits, h]

-- LLM HELPER
lemma count_even_odd_digits_pos (n : Nat) :
  n > 0 → 
  let digit := n % 10
  let (even_rest, odd_rest) := count_even_odd_digits (n / 10)
  count_even_odd_digits n = 
    if digit % 2 = 0 then (even_rest + 1, odd_rest)
    else (even_rest, odd_rest + 1) := by
  intro h
  simp only [count_even_odd_digits]
  rw [if_neg (ne_of_gt h)]

-- LLM HELPER
lemma implementation_components (num : Int) :
  let n := |num|.toNat
  let (even_count, odd_count) := count_even_odd_digits n
  implementation num = (Int.ofNat even_count, Int.ofNat odd_count) := by
  simp only [implementation]

theorem correctness
(num: Int)
: problem_spec implementation num := by
  simp only [problem_spec]
  use implementation num
  constructor
  · rfl
  · simp only [implementation]
    let n := |num|.toNat
    let (even_count, odd_count) := count_even_odd_digits n
    constructor
    · simp only [Int.natAbs_eq]
      rfl
    constructor
    · intro h
      constructor
      · constructor
        · intro h_even
          simp only [Int.natAbs_eq] at *
          sorry
        · intro h_eq
          simp only [Int.natAbs_eq] at *
          sorry
      · constructor
        · intro h_odd
          simp only [Int.natAbs_eq] at *
          sorry
        · intro h_eq
          simp only [Int.natAbs_eq] at *
          sorry
    · intro h
      constructor
      · constructor
        · intro h_odd
          simp only [Int.natAbs_eq] at *
          sorry
        · intro h_eq
          simp only [Int.natAbs_eq] at *
          sorry
      · constructor
        · intro h_even
          simp only [Int.natAbs_eq] at *
          sorry
        · intro h_eq
          simp only [Int.natAbs_eq] at *
          sorry