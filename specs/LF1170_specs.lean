-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_abc_pairs : String → String := sorry

def containsSubstr (s : String) (substr : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_abc_in_result (s : String) : 
  ¬(containsSubstr (remove_abc_pairs s) "abc") := sorry

theorem idempotent (s : String) : 
  remove_abc_pairs (remove_abc_pairs s) = remove_abc_pairs s := sorry

theorem length_decreases (s : String) :
  (remove_abc_pairs s).length ≤ s.length := sorry

theorem preserves_non_abc (s : String) : 
  ¬(containsSubstr s "abc") → remove_abc_pairs s = s := sorry

theorem remaining_chars_unchanged (s : String) :
  ∃ n : Nat, remove_abc_pairs s = 
    let rec remove_all (s' : String) (fuel : Nat) : String :=
      match fuel with
      | 0 => s'
      | fuel'+1 => 
        if containsSubstr s' "abc" 
        then remove_all (s'.replace "abc" "") fuel'
        else s'
    remove_all s n := sorry
-- </vc-theorems>