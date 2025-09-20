-- <vc-preamble>
def switcher (arr : List Nat) : String := sorry

def is_valid_input (arr : List Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_output (s : String) : Bool := sorry

def expected_map (n : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem switcher_properties (arr : List Nat) : 
  is_valid_input arr → 
  let result := switcher arr
  (is_valid_output result) ∧ 
  (result.length = (arr.filter (· ≠ 0)).length) ∧
  (result = String.join (arr.map expected_map)) := sorry

theorem switcher_all_zeros (arr : List Nat) :
  arr.all (· = 0) →
  switcher arr = "" := sorry
-- </vc-theorems>