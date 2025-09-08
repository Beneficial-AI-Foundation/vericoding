import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def nat_to_binary (n : Nat) : List Char :=
  if n = 0 then ['0']
  else (Nat.digits 2 n).map (fun d => if d = 0 then '0' else '1')

def implementation (n: Nat) : String :=
  let digit_sum := (Nat.digits 10 n).sum
  String.mk (nat_to_binary digit_sum)

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result : String) :=
  0 < n →
  result.all (fun c => c = '0' ∨ c = '1') →
  Nat.ofDigits 2 (result.data.map (fun c => if c = '0' then 0 else 1)).reverse = (Nat.digits 10 n).sum
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
lemma binary_chars_valid (n : Nat) : 
  (String.mk (nat_to_binary n)).all (fun c => c = '0' ∨ c = '1') := by
  simp [String.all, nat_to_binary]
  split
  · rfl
  · simp [List.all_map]
    intro d _
    split <;> simp

-- LLM HELPER  
lemma nat_to_binary_correct (n : Nat) :
  Nat.ofDigits 2 ((String.mk (nat_to_binary n)).data.map (fun c => if c = '0' then 0 else 1)).reverse = n := by
  simp [nat_to_binary]
  split
  case isTrue h =>
    rw [h]
    rfl
  case isFalse h =>
    simp only [String.data_mk, List.map_map, List.map_reverse]
    have h_map : (fun d => if (if d = 0 then '0' else '1') = '0' then 0 else 1) = id := by
      ext d
      split
      · split <;> simp
      · split <;> simp
    rw [h_map, List.map_id]
    exact Nat.ofDigits_digits 2 (by norm_num) _

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use String.mk (nat_to_binary (Nat.digits 10 n).sum)
  constructor
  · rfl
  · intro h_pos
    constructor
    · exact binary_chars_valid _
    · exact nat_to_binary_correct _

-- #test implementation 1000 = "1"
-- #test implementation 150 = "110"
-- #test implementation 147 = "1100"