-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isUpperCase (c : Char) : Bool :=
  sorry

def toLetterIndex (c : Char) : Nat :=
  sorry

def new_numeral_system (letter : Char) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem correct_format {letter : Char} :
  ∀ s ∈ new_numeral_system letter,
    s.length = 5 ∧ s.data.get ⟨1, sorry⟩ = ' ' ∧
    s.data.get ⟨2, sorry⟩ = '+' ∧
    s.data.get ⟨3, sorry⟩ = ' ' := by
  sorry

theorem valid_letters {letter : Char} :
  ∀ s ∈ new_numeral_system letter,
    let first := s.data.get ⟨0, sorry⟩
    let last := s.data.get ⟨4, sorry⟩
    isUpperCase first ∧
    isUpperCase last ∧
    first ≤ letter ∧
    last ≤ letter := by
  sorry

theorem correct_sum {letter : Char} :
  ∀ s ∈ new_numeral_system letter,
    let first := s.data.get ⟨0, sorry⟩
    let last := s.data.get ⟨4, sorry⟩
    toLetterIndex first + toLetterIndex last = toLetterIndex letter := by
  sorry

theorem left_side_sorted {letter : Char} :
  let leftSide := (new_numeral_system letter).map (fun s => s.data.get ⟨0, sorry⟩)
  ∀ i j, i < j → j < leftSide.length → leftSide[i]! ≤ leftSide[j]! := by
  sorry

theorem middle_pair_equal {letter : Char} :
  toLetterIndex letter % 2 = 0 →
    let result := new_numeral_system letter
    let midIdx := toLetterIndex letter / 2
    let middle := result[midIdx]!
    middle.data.get ⟨0, sorry⟩ = middle.data.get ⟨4, sorry⟩ := by
  sorry
-- </vc-theorems>