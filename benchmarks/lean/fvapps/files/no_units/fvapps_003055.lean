-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def change (s : String) : String := sorry 

theorem change_output_format (s : String) : 
  let result := change s
  (result.length = 26) ∧ 
  (∀ c ∈ result.data, c = '0' ∨ c = '1')  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem change_letter_detection (s : String) (i : Nat) (h : i < 26) :
  let result := change s
  let letter := Char.ofNat (i + 'a'.toNat)
  (result.data.get! i) = if letter ∈ s.toLower.data then '1' else '0' := sorry

theorem change_empty_string :
  change "" = String.mk (List.replicate 26 '0') := sorry

theorem change_all_lowercase (s : String) (h : ∀ c ∈ s.data, 'a' ≤ c ∧ c ≤ 'z') :
  let result := change s
  ∀ i, i < 26 →
    let c := Char.ofNat (i + 'a'.toNat)
    if c ∈ s.data 
    then (result.data.get! i) = '1'
    else True := sorry
-- </vc-theorems>