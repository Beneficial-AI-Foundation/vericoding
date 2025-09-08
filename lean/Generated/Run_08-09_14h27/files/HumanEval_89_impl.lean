/- 
function_signature: "def encrypt(str : str) -> str"
docstring: |
    Create a function encrypt that takes a string as an argument and
    returns a string encrypted with the alphabet being rotated.
    The alphabet should be rotated in a manner such that the letters
    shift down by two multiplied to two places.
test_cases:
  - input: "hi"
    output: "lm"
  - input: "asdfghjkl"
    output: "ewhjklnop"
  - input: "gf"
    output: "kj"
  - input: "et"
    output: "ix"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def shift_char (c : Char) : Char :=
  if c.isLower then
    let offset := c.toNat - 97
    let shifted := (offset + 4) % 26
    Char.ofNat (shifted + 97)
  else c

def implementation (str: String) : String :=
  String.mk (str.data.map shift_char)

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(str: String) :=
-- spec
let spec (result : String) :=
  result.data.all (fun c => c.isLower) →
  result.length = str.length ∧
  (∀ i, i < str.length →
    let c := str.data[i]!
    let c' := result.data[i]!
    ((c'.toNat - 97) + 2 * 2) % 26 = (c.toNat - 97))
-- program termination
∃ result,
  implementation str = result ∧
  spec result

-- LLM HELPER
lemma shift_char_spec (c : Char) (h : c.isLower) :
  let c' := shift_char c
  c'.isLower ∧ ((c'.toNat - 97) + 2 * 2) % 26 = (c.toNat - 97) := by
  simp [shift_char, h]
  constructor
  · simp [Char.isLower]
    have h1 : c.toNat ≥ 97 := by
      simp [Char.isLower] at h
      exact h.1
    have h2 : c.toNat ≤ 122 := by
      simp [Char.isLower] at h
      exact h.2
    have offset_bound : (c.toNat - 97) < 26 := by
      have : c.toNat ≤ 122 := h2
      omega
    have shifted_bound : ((c.toNat - 97) + 4) % 26 < 26 := Nat.mod_lt _ (by norm_num)
    constructor
    · have : 97 + ((c.toNat - 97) + 4) % 26 ≥ 97 := by
        have : ((c.toNat - 97) + 4) % 26 ≥ 0 := Nat.zero_le _
        omega
      have : (Char.ofNat (((c.toNat - 97) + 4) % 26 + 97)).val = (((c.toNat - 97) + 4) % 26 + 97) % 256 := by
        rfl
      rw [this]
      have bound : ((c.toNat - 97) + 4) % 26 + 97 ≤ 122 := by
        have : ((c.toNat - 97) + 4) % 26 < 26 := shifted_bound
        omega
      have : ((c.toNat - 97) + 4) % 26 + 97 < 256 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
    · have : 97 + ((c.toNat - 97) + 4) % 26 ≤ 122 := by
        have : ((c.toNat - 97) + 4) % 26 < 26 := shifted_bound
        omega
      have : (Char.ofNat (((c.toNat - 97) + 4) % 26 + 97)).val = (((c.toNat - 97) + 4) % 26 + 97) % 256 := by
        rfl
      rw [this]
      have bound : ((c.toNat - 97) + 4) % 26 + 97 ≤ 122 := by
        have : ((c.toNat - 97) + 4) % 26 < 26 := shifted_bound
        omega
      have : ((c.toNat - 97) + 4) % 26 + 97 < 256 := by omega
      rw [Nat.mod_eq_of_lt this]
      exact bound
  · have : (Char.ofNat (((c.toNat - 97) + 4) % 26 + 97)).toNat = (((c.toNat - 97) + 4) % 26 + 97) % 256 := by
      rfl
    have bound : ((c.toNat - 97) + 4) % 26 + 97 < 256 := by
      have : ((c.toNat - 97) + 4) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega
    rw [this, Nat.mod_eq_of_lt bound]
    have eq_div_mod : (c.toNat - 97) + 4 = ((c.toNat - 97) + 4) % 26 + 26 * (((c.toNat - 97) + 4) / 26) := by
      exact Nat.mod_add_div _ _
    omega

theorem correctness
(str: String)
: problem_spec implementation str := by
  simp [problem_spec, implementation]
  use String.mk (str.data.map shift_char)
  constructor
  · rfl
  · intro h_all_lower
    constructor
    · simp [String.length]
    · intro i h_i
      simp [String.data, String.get!]
      rw [List.get!_map]
      let c := str.data[i]!
      let c' := shift_char c
      have h_lower : c.isLower := by
        have h_mem : c ∈ str.data := List.get!_mem str.data i h_i
        exact h_all_lower c h_mem
      have spec := shift_char_spec c h_lower
      exact spec.2

-- #test implementation "hi" = "lm"
-- #test implementation "asdfghjkl" = "ewhjklnop"
-- #test implementation "gf" = "kj"
-- #test implementation "et" = "ix"