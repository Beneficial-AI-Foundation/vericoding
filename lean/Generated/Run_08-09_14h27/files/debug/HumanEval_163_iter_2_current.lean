import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def range_even (start : Nat) (stop : Nat) : List Nat :=
  let min_val := min start stop
  let max_val := max start stop
  if min_val = max_val ∧ min_val % 2 = 1 then
    []
  else
    let first_even := if min_val % 2 = 0 then min_val else min_val + 1
    let last_even := if max_val % 2 = 0 then max_val else max_val - 1
    if first_even > last_even then
      []
    else
      List.range ((last_even - first_even) / 2 + 1) |>.map (fun i => first_even + 2 * i)

def implementation (a b: Nat) : List Nat :=
  range_even a b

def problem_spec
-- function signature
(impl: Nat → Nat → List Nat)
-- inputs
(a b : Nat) :=
let isAscendingBy2 (r : List Nat) :=
∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2
-- spec
let spec (result: List Nat) :=
result.all (fun n => decide (n % 2 = 0)) = true ∧ isAscendingBy2 result ∧
1 < result.length ∧
let min_a_b := min a b;
let max_a_b := max a b;
if min_a_b = max_a_b ∧ (min_a_b % 2 = 1)
then result = []
else ((result[0]! = if 2 ∣ min_a_b then min_a_b else (min_a_b + 1)) ∧
(result[result.length-1]! = if 2 ∣ max_a_b then max_a_b else max_a_b - 1))
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma range_even_all_even (start stop : Nat) :
  (range_even start stop).all (fun n => decide (n % 2 = 0)) = true := by
  unfold range_even
  simp only [List.all_eq_true]
  intro x hx
  by_cases h : min start stop = max start stop ∧ min start stop % 2 = 1
  · simp [h] at hx
  · simp [h] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    simp [decide_eq_true_iff, Nat.add_mod, Nat.mul_mod]

-- LLM HELPER  
lemma range_even_ascending (start stop : Nat) :
  let r := range_even start stop
  ∀ i, i < r.length - 1 → r[i+1]! - r[i]! = 2 := by
  intro i hi
  simp only [range_even] at hi ⊢
  by_cases h : min start stop = max start stop ∧ min start stop % 2 = 1
  · simp [h] at hi
  · simp [h] at hi ⊢
    have : i < (List.range ((if max start stop % 2 = 0 then max start stop else max start stop - 1) - (if min start stop % 2 = 0 then min start stop else min start stop + 1)) / 2 + 1).length - 1 := by
      simpa using hi
    simp [List.get_map, List.get_range]
    ring

theorem correctness
(a b: Nat)
: problem_spec implementation a b := by
  use implementation a b
  constructor
  · rfl
  · simp only [problem_spec, implementation]
    constructor
    · exact range_even_all_even a b
    constructor  
    · exact range_even_ascending a b
    constructor
    · simp only [range_even]
      by_cases h : min a b = max a b ∧ min a b % 2 = 1
      · simp [h]
      · simp [h]
        have : (List.range ((if max a b % 2 = 0 then max a b else max a b - 1) - (if min a b % 2 = 0 then min a b else min a b + 1)) / 2 + 1).length ≥ 2 := by
          simp only [List.length_range]
          omega
        omega
    · by_cases h : min a b = max a b ∧ min a b % 2 = 1
      · simp [h, range_even]
      · simp [h, range_even]
        constructor
        · simp [List.get_map, List.get_range]
        · simp [List.get_map, List.get_range, List.length_map, List.length_range]
          ring