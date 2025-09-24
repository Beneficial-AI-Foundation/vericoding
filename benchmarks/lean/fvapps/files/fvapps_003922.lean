-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Bool :=
sorry

def countOccurrences (c : Char) (s : String) : Nat :=
sorry

def allCountsEqual (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_exists_char_removal
  {s : String}
  (h1 : solve s = true)
  (h2 : s.length ≥ 2) :
  ∃ c : Char, c ∈ s.data ∧
  allCountsEqual (s.replace (String.mk [c]) "") = true :=
sorry

theorem solve_equal_counts_after_removal
  {s : String}
  (h1 : solve s = true)
  (h2 : s.length ≥ 2) :
  ∃ c : Char, c ∈ s.data ∧
  let s' := s.replace (String.mk [c]) ""
  (∀ c₁ c₂, c₁ ∈ s'.data → c₂ ∈ s'.data →
    countOccurrences c₁ s' = countOccurrences c₂ s') :=
sorry
-- </vc-theorems>