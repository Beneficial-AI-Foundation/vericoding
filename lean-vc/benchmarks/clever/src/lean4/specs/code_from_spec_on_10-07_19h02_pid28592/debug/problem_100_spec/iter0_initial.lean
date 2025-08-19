import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  result.length = n ∧
  (forall i: Nat, (1 <= i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def buildSequence (n: Int) : List Int :=
  if n <= 0 then []
  else List.range n.natAbs |>.map (fun i => n + 2 * i)

def implementation (n: Int) : List Int := buildSequence n

-- LLM HELPER
lemma buildSequence_length (n: Int) (h: n > 0) : (buildSequence n).length = n := by
  simp [buildSequence]
  split_ifs
  · contradiction
  · simp [List.length_map, List.length_range]

-- LLM HELPER
lemma buildSequence_get (n: Int) (h: n > 0) (i: Nat) (hi: i < n) : 
  (buildSequence n)[i]! = n + 2 * i := by
  simp [buildSequence]
  split_ifs
  · contradiction
  · simp [List.getElem_map, List.getElem_range]

-- LLM HELPER
lemma buildSequence_recurrence (n: Int) (h: n > 0) (i: Nat) (hi1: 1 <= i) (hi2: i < n) :
  (buildSequence n)[i]! = (buildSequence n)[i-1]! + 2 := by
  have h1 : i - 1 < n := Nat.sub_lt_of_pos_le hi2 hi1
  rw [buildSequence_get n h i hi2, buildSequence_get n h (i-1) h1]
  ring

-- LLM HELPER
lemma buildSequence_first (n: Int) (h: n > 0) : (buildSequence n)[0]! = n := by
  rw [buildSequence_get n h 0 (Int.natAbs_pos.mpr (ne_of_gt h))]
  ring

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  if h : n <= 0 then
    use []
    simp [buildSequence, h]
    constructor
    · rfl
    · constructor
      · simp
      · simp
  else
    push_neg at h
    use buildSequence n
    constructor
    · rfl
    · constructor
      · exact buildSequence_length n h
      · constructor
        · intros i hi
          exact buildSequence_recurrence n h i hi.1 (Int.natCast_lt.mp hi.2)
        · exact buildSequence_first n h