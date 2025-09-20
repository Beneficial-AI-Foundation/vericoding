-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nth_occurrence (substring : String) (string : String) (occurrence : Nat) : Int := sorry

theorem find_nth_occurrence_result_valid {string substring : String} {occurrence : Nat}
    (h : substring.length > 0) :
  let result := find_nth_occurrence substring string occurrence
  result = -1 ∨ (0 ≤ result ∧ result < string.length) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_nth_occurrence_substring_exists {string substring : String} {occurrence : Nat}
    (h : substring.length > 0)
    (h2 : find_nth_occurrence substring string occurrence ≠ -1) :
  let result := find_nth_occurrence substring string occurrence
  ∃ (pos : String.Pos), 
    pos.byteIdx = result.toNat ∧ 
    string.extract pos (String.Pos.mk (result.toNat + substring.length)) = substring := sorry

theorem find_nth_occurrence_earlier_exist {string substring : String} {occurrence : Nat}
    (h : substring.length > 0)
    (h2 : find_nth_occurrence substring string occurrence ≠ -1) :
  ∀ i, 1 ≤ i → i < occurrence → 
    let prev := find_nth_occurrence substring string i
    prev ≠ -1 ∧ prev < find_nth_occurrence substring string occurrence := sorry

theorem occurrence_ordering {string substring : String}
    (h : substring.length > 0) :
  let second := find_nth_occurrence substring string 2
  second ≠ -1 →
    let first := find_nth_occurrence substring string 1
    first ≠ -1 ∧ first < second := sorry
-- </vc-theorems>