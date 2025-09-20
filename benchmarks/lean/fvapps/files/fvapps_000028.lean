-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_abacaba_substring (s : String) : Nat := sorry

def find_abacaba_substring (n : Nat) (s : String) : Bool × String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_abacaba_nonnegative (s : String) :
  check_abacaba_substring s ≥ 0 := sorry

theorem check_abacaba_count_correct (s : String) :
  check_abacaba_substring s = s.length := sorry  -- simplified as String.countSubstr not available

theorem find_abacaba_output_valid {n : Nat} {s : String} :
  let (success, result) := find_abacaba_substring n s
  success →
    result.length = n ∧ 
    ¬result.contains '?' ∧
    check_abacaba_substring result = 1 ∧
    ∀ (i : String.Pos), s.get i ≠ '?' → s.get i = result.get i := sorry

theorem find_abacaba_impossible {n : Nat} {s : String} :
  let (success, result) := find_abacaba_substring n s
  ¬success →
    result = "" ∧
    (∀ c ∈ ['a', 'b', 'c', 'z'], 
      let test_s := s.replace "?" (String.mk [c])
      check_abacaba_substring test_s ≠ 1) := sorry
-- </vc-theorems>