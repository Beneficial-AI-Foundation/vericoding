/- 
function_signature: "def cycpattern_check(String a, String b) -> Bool"
docstring: |
    You are given 2 words. You need to return True if the second word or any of its rotations is a substring in the first word, else False
test_cases:
  - input: ["abcd", "abd"]
    expected_output: False
  - input: ["hello", "ell"]
    expected_output: True
  - input: ["whassup", "psus"]
    expected_output: False
  - input: ["abab", "baa"]
    expected_output: True
  - input: ["efef", "eeff"]
    expected_output: False
  - input: ["himenss", "simen"]
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def get_all_rotations (s: String) : List String :=
  let n := s.length
  if n = 0 then []
  else List.range n |>.map (fun i => s.drop i ++ s.take i)

-- LLM HELPER  
def any_rotation_is_substring (a b: String) : Bool :=
  if b.length = 0 then true
  else (get_all_rotations b).any (fun rotation => a.containsSubstr rotation)

def implementation (a b: String) : Bool :=
  any_rotation_is_substring a b

def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(a b: String) :=
-- spec
let spec (result: Bool) :=
(b.length = 0 → result) ∧
(0 < b.length →
result ↔ ((b.length ≤ a.length) ∧
  (∃ i : Nat, i < b.length ∧
  let b_rotation := b.drop i ++ b.take i;
  a.containsSubstr b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma get_all_rotations_mem (b: String) (i: Nat) (h: i < b.length) :
  b.drop i ++ b.take i ∈ get_all_rotations b := by
  unfold get_all_rotations
  simp [List.mem_map, List.mem_range]
  use i
  exact ⟨h, rfl⟩

-- LLM HELPER
lemma get_all_rotations_exists (b: String) (rotation: String) :
  rotation ∈ get_all_rotations b → 
  ∃ i : Nat, i < b.length ∧ rotation = b.drop i ++ b.take i := by
  unfold get_all_rotations
  simp only [List.mem_map, List.mem_range]
  intro ⟨i, hi, heq⟩
  use i
  exact ⟨hi, heq.symm⟩

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  unfold problem_spec implementation any_rotation_is_substring
  use (if b.length = 0 then true else (get_all_rotations b).any (fun rotation => a.containsSubstr rotation))
  constructor
  · simp
  · constructor
    · intro h
      simp [h]
    · intro h_pos
      constructor
      · intro h_impl
        simp [h_pos] at h_impl
        constructor
        · by_contra h_not_le
          simp at h_not_le
          have : get_all_rotations b = [] := by
            unfold get_all_rotations
            simp [Nat.not_lt.mp (le_of_not_gt h_not_le)]
          simp [this] at h_impl
        · have h_any := List.any_eq_true.mp h_impl
          obtain ⟨rotation, h_mem, h_substr⟩ := h_any
          have ⟨i, hi, heq⟩ := get_all_rotations_exists b rotation h_mem
          use i
          exact ⟨hi, heq ▸ h_substr⟩
      · intro ⟨h_le, i, hi, h_substr⟩
        simp [h_pos]
        apply List.any_eq_true.mpr
        use b.drop i ++ b.take i
        exact ⟨get_all_rotations_mem b i hi, h_substr⟩

-- #test implementation "abcd" "abd" = False
-- #test implementation "hello" "ell" = True
-- #test implementation "whassup" "psus" = False
-- #test implementation "abab" "baa" = True
-- #test implementation "efef" "eeff" = False
-- #test implementation "himenss" "simen" = True