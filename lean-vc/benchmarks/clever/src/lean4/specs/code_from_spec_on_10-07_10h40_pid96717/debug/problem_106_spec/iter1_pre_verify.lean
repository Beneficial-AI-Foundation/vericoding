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
  (result.length = n) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Even i) → (result[i-1]! = Nat.factorial i)) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Odd i) → (result[i-1]! = (List.range (i+1)).sum))
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def compute_element (i: Nat) : Int :=
  if Even i then (Nat.factorial i : Int) else ((List.range (i+1)).sum : Int)

def implementation (n: Int) : List Int := 
  if n ≤ 0 then [] else (List.range n.natAbs).map (fun i => compute_element (i + 1))

-- LLM HELPER
lemma range_map_length (n: Nat) : ((List.range n).map (fun i => compute_element (i + 1))).length = n := by
  simp [List.length_map, List.length_range]

-- LLM HELPER
lemma get_range_map (n: Nat) (i: Nat) (h: i < n) : 
  ((List.range n).map (fun j => compute_element (j + 1)))[i]! = compute_element (i + 1) := by
  simp [List.get_map, List.get_range]

-- LLM HELPER
lemma natAbs_pos_of_pos (n: Int) (h: 0 < n) : 0 < n.natAbs := by
  exact Int.natAbs_pos.mpr (ne_of_gt h)

-- LLM HELPER
lemma natAbs_le_iff (n: Int) (k: Nat) (h: 0 ≤ n) : k ≤ n ↔ k ≤ n.natAbs := by
  rw [← Int.natAbs_of_nonneg h]
  exact Int.natCast_le

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec
  unfold implementation
  split_ifs with h
  · -- case n ≤ 0
    use []
    simp
    intro i hi
    omega
  · -- case n > 0
    push_neg at h
    have n_pos : 0 < n := h
    have n_nonneg : 0 ≤ n := le_of_lt n_pos
    use (List.range n.natAbs).map (fun i => compute_element (i + 1))
    constructor
    · rfl
    · constructor
      · -- length condition
        rw [range_map_length]
        rw [Int.natAbs_of_nonneg n_nonneg]
      · constructor
        · -- even case
          intro i hi
          have i_lt : i - 1 < n.natAbs := by
            rw [Int.natAbs_of_nonneg n_nonneg]
            omega
          have i_ge : 0 ≤ i - 1 := by omega
          rw [get_range_map n.natAbs (i - 1) i_lt]
          simp [compute_element]
          rw [if_pos hi.2.2]
          omega
        · -- odd case
          intro i hi
          have i_lt : i - 1 < n.natAbs := by
            rw [Int.natAbs_of_nonneg n_nonneg]
            omega
          have i_ge : 0 ≤ i - 1 := by omega
          rw [get_range_map n.natAbs (i - 1) i_lt]
          simp [compute_element]
          rw [if_neg]
          · omega
          · exact Nat.not_even_iff.mpr hi.2.2