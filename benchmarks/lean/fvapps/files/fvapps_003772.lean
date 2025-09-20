-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_missing_letter (chars : List Char) : Option Char := sorry

theorem find_missing_letter_with_gap {chars : List Char} 
    (h₁ : chars.length > 1)
    (h₂ : ∀ i j, i < j → j < chars.length → Char.toNat (chars.get! i) < Char.toNat (chars.get! j))
    (h₃ : ∀ (i : Nat), i + 1 < chars.length → 
          Char.toNat (chars.get! i) + 1 = Char.toNat (chars.get! (i + 1))) :
    let missing := chars.get! 0
    let test_input := chars.get! 0 :: chars.tail!
    find_missing_letter test_input = some missing := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_missing_letter_consecutive {chars : List Char}
    (h₁ : chars.length > 1) 
    (h₂ : ∀ i j, i < j → j < chars.length → Char.toNat (chars.get! i) < Char.toNat (chars.get! j))
    (h₃ : ∀ (i : Nat), i + 1 < chars.length → 
          Char.toNat (chars.get! i) + 1 = Char.toNat (chars.get! (i + 1))) :
    find_missing_letter chars = none := sorry
-- </vc-theorems>