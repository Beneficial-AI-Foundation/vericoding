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
  simp [shift_char]
  split_ifs with h_lower
  · simp
    constructor
    · -- prove c' is lowercase
      simp [Char.isLower]
      have h1 : c.toNat ≥ 97 := by
        simp [Char.isLower] at h
        exact h.1
      have h2 : c.toNat ≤ 122 := by
        simp [Char.isLower] at h
        exact h.2
      have offset_bound : (c.toNat - 97) < 26 := by
        omega
      have shifted_bound : ((c.toNat - 97) + 4) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      constructor
      · omega
      · omega
    · -- prove the shift property
      have offset_eq : (c.toNat - 97) + 4 = ((c.toNat - 97) + 4) % 26 + 26 * (((c.toNat - 97) + 4) / 26) := by
        rw [Nat.div_add_mod]
      rw [Nat.add_mod]
      simp
      ring
  · contradiction

-- LLM HELPER  
lemma map_preserves_length {α β : Type} (f : α → β) (l : List α) :
  (l.map f).length = l.length := List.length_map

-- LLM HELPER
lemma get_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  rw [List.get!_eq_get_or_else, List.get!_eq_get_or_else]
  have h_map : i < (l.map f).length := by
    rw [List.length_map]
    exact h
  rw [List.get?_map, Option.get_or_else_map]
  simp [List.get?_eq_some h]

theorem correctness
(str: String)
: problem_spec implementation str
:= by
  simp [problem_spec, implementation]
  use String.mk (str.data.map shift_char)
  constructor
  · rfl
  · intro h_all_lower
    constructor
    · simp [String.length]
      exact map_preserves_length shift_char str.data
    · intro i h_i
      simp [String.data, String.get!]
      have h_map_len : i < (str.data.map shift_char).length := by
        rw [List.length_map]
        exact h_i
      rw [get_map shift_char str.data i h_i]
      let c := str.data[i]!
      let c' := shift_char c
      have h_lower : c.isLower := by
        have h_all : (String.mk (str.data.map shift_char)).data.all (fun c => c.isLower) := h_all_lower
        simp [String.data] at h_all
        have h_c' : c' ∈ str.data.map shift_char := by
          rw [List.mem_map]
          use c
          constructor
          · exact List.get!_mem str.data i
          · rfl
        exact List.all_imp_forall h_all h_c'
      have spec := shift_char_spec c h_lower
      exact spec.2

-- #test implementation "hi" = "lm"
-- #test implementation "asdfghjkl" = "ewhjklnop"
-- #test implementation "gf" = "kj"
-- #test implementation "et" = "ix"