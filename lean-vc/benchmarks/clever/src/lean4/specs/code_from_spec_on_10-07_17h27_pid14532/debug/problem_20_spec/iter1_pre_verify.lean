import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → (Rat × Rat))
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: (Rat × Rat)) :=
2 ≤ numbers.length →
(let (smaller, larger) := result;
let abs_diff := |larger - smaller|;
smaller ≤ larger ∧
smaller ∈ numbers ∧
larger ∈ numbers ∧
(∀ x y, x ∈ numbers → y ∈ numbers →  abs_diff ≤ |x - y|) ∧
(smaller = larger → 1 ≤ (numbers.filter (fun z => z = smaller)).length));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_diff_pair (numbers: List Rat) : (Rat × Rat) :=
  match numbers with
  | [] => (0, 0)
  | [x] => (x, x)
  | x :: xs => 
    let candidates := (x :: xs).bind (fun a => (x :: xs).map (fun b => (min a b, max a b)))
    let valid_pairs := candidates.filter (fun p => p.1 ∈ numbers ∧ p.2 ∈ numbers)
    match valid_pairs with
    | [] => (x, x)
    | p :: ps => ps.foldl (fun acc pair => 
      if |pair.2 - pair.1| < |acc.2 - acc.1| then pair else acc) p

def implementation (numbers: List Rat): (Rat × Rat) := 
  find_min_diff_pair numbers

-- LLM HELPER
lemma min_le_max (a b : Rat) : min a b ≤ max a b := by
  simp [min_def, max_def]
  split_ifs <;> linarith

-- LLM HELPER
lemma min_mem_of_mem (a b : Rat) (h1 : a ∈ numbers) (h2 : b ∈ numbers) : 
  min a b ∈ numbers := by
  simp [min_def]
  split_ifs
  · exact h1
  · exact h2

-- LLM HELPER
lemma max_mem_of_mem (a b : Rat) (h1 : a ∈ numbers) (h2 : b ∈ numbers) : 
  max a b ∈ numbers := by
  simp [max_def]
  split_ifs
  · exact h2
  · exact h1

-- LLM HELPER
lemma abs_diff_nonneg (a b : Rat) : 0 ≤ |a - b| := abs_nonneg _

-- LLM HELPER
lemma find_min_diff_pair_spec (numbers : List Rat) (h : 2 ≤ numbers.length) :
  let result := find_min_diff_pair numbers
  let (smaller, larger) := result
  let abs_diff := |larger - smaller|
  smaller ≤ larger ∧
  smaller ∈ numbers ∧
  larger ∈ numbers ∧
  (∀ x y, x ∈ numbers → y ∈ numbers → abs_diff ≤ |x - y|) ∧
  (smaller = larger → 1 ≤ (numbers.filter (fun z => z = smaller)).length) := by
  sorry

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use find_min_diff_pair numbers
  constructor
  · rfl
  · intro h
    exact find_min_diff_pair_spec numbers h