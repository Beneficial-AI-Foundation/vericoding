def problem_spec
-- function signature
(implementation: String → String → String)
-- inputs
(a b: String) :=
-- spec
let spec (result: String) :=
  a.all (fun c => c = '0' ∨ c = '1') →
  b.all (fun c => c = '0' ∨ c = '1') →
  a.length = b.length →
  result.length = a.length ∧
  result.all (fun c => c = '0' ∨ c = '1') ∧
  (∀ i, i < a.length →
  let i_pos := String.Pos.mk i;
  (a.get i_pos = b.get i_pos → result.get i_pos = '0') ∧
  (a.get i_pos ≠ b.get i_pos → result.get i_pos = '1'));
-- program termination
∃ result, implementation a b = result ∧
spec result

-- LLM HELPER
def xor_char (c1 c2: Char) : Char :=
  if c1 = c2 then '0' else '1'

-- LLM HELPER
def xor_strings_aux (a b: String) (i: Nat) : String :=
  if i = 0 then ""
  else
    let prev := xor_strings_aux a b (i - 1)
    let pos := String.Pos.mk (i - 1)
    prev.push (xor_char (a.get pos) (b.get pos))

def implementation (a b: String) : String := 
  xor_strings_aux a b a.length

-- LLM HELPER
lemma xor_strings_aux_length (a b: String) (n: Nat) : 
  (xor_strings_aux a b n).length = n := by
  induction n with
  | zero => simp [xor_strings_aux]
  | succ n ih => 
    simp [xor_strings_aux]
    rw [String.length_push, ih]

-- LLM HELPER
lemma xor_strings_aux_all_binary (a b: String) (n: Nat) :
  (xor_strings_aux a b n).all (fun c => c = '0' ∨ c = '1') := by
  induction n with
  | zero => simp [xor_strings_aux, String.all]
  | succ n ih =>
    simp [xor_strings_aux]
    rw [String.all_push]
    constructor
    · exact ih
    · simp [xor_char]
      split
      · simp
      · simp

-- LLM HELPER  
lemma xor_strings_aux_get (a b: String) (n: Nat) (i: Nat) (hi: i < n) :
  let pos := String.Pos.mk i
  (xor_strings_aux a b n).get pos = xor_char (a.get pos) (b.get pos) := by
  induction n generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    simp [xor_strings_aux]
    by_cases h : i = n
    · subst h
      rw [String.get_push_eq]
      rw [xor_strings_aux_length]
    · have hi' : i < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) (Ne.symm h)
      rw [String.get_push_lt]
      · exact ih i hi'
      · rw [xor_strings_aux_length]
        exact hi'

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  simp [problem_spec, implementation]
  use xor_strings_aux a b a.length
  constructor
  · rfl
  · intro ha hb hab
    constructor
    · rw [xor_strings_aux_length]
    constructor
    · exact xor_strings_aux_all_binary a b a.length
    · intro i hi
      simp [String.Pos.mk]
      constructor
      · intro h
        rw [xor_strings_aux_get a b a.length i hi]
        simp [xor_char, h]
      · intro h
        rw [xor_strings_aux_get a b a.length i hi]
        simp [xor_char]
        split
        · rename_i h'
          contradiction
        · rfl