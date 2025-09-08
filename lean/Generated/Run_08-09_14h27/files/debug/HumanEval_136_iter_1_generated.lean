import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def find_largest_negative (lst: List Int) : Option Int :=
  lst.filter (· < 0) |>.maximum?

-- LLM HELPER  
def find_smallest_positive (lst: List Int) : Option Int :=
  lst.filter (· > 0) |>.minimum?

def implementation (lst: List Int) : (Option Int × Option Int) :=
  (find_largest_negative lst, find_smallest_positive lst)

def problem_spec
-- function signature
(impl: List Int → Option Int × Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: Option Int × Option Int) :=
  let (a, b) := result;
  (match a with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a) ∧
  (match b with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i)
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma filter_maximum_some_iff {lst : List Int} {a : Int} :
  (lst.filter (· < 0)).maximum? = some a ↔ 
  a ∈ lst ∧ a < 0 ∧ ∀ i ∈ lst, i < 0 → i ≤ a := by
  simp [List.maximum?_eq_some_iff, List.mem_filter]
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1.1, h1.2, fun i hi1 hi2 => h3 i ⟨hi1, hi2⟩⟩
  · intro ⟨h1, h2, h3⟩  
    exact ⟨⟨h1, h2⟩, h3, fun i hi => h3 i hi.1 hi.2⟩

-- LLM HELPER
lemma filter_maximum_none_iff {lst : List Int} :
  (lst.filter (· < 0)).maximum? = none ↔ ¬(∃ i, i ∈ lst ∧ i < 0) := by
  simp [List.maximum?_eq_none_iff, List.filter_eq_nil_iff]

-- LLM HELPER
lemma filter_minimum_some_iff {lst : List Int} {b : Int} :
  (lst.filter (· > 0)).minimum? = some b ↔ 
  b ∈ lst ∧ 0 < b ∧ ∀ i ∈ lst, 0 < i → b ≤ i := by
  simp [List.minimum?_eq_some_iff, List.mem_filter]
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1.1, h1.2, fun i hi1 hi2 => h3 i ⟨hi1, hi2⟩⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3, fun i hi => h3 i hi.1 hi.2⟩

-- LLM HELPER
lemma filter_minimum_none_iff {lst : List Int} :
  (lst.filter (· > 0)).minimum? = none ↔ ¬(∃ i, i ∈ lst ∧ 0 < i) := by
  simp [List.minimum?_eq_none_iff, List.filter_eq_nil_iff]

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec implementation find_largest_negative find_smallest_positive
  use (lst.filter (· < 0)).maximum?, (lst.filter (· > 0)).minimum?
  constructor
  · simp
  · simp
    constructor
    · cases h : (lst.filter (· < 0)).maximum?
      · simp [filter_maximum_none_iff.mp h]
      · simp [filter_maximum_some_iff.mp h]
    · cases h : (lst.filter (· > 0)).minimum?  
      · simp [filter_minimum_none_iff.mp h]
      · simp [filter_minimum_some_iff.mp h]