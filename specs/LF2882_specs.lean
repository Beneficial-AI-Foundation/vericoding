-- <vc-preamble>
def isSorted (cs : List Char) : Prop :=
  ∀ i j, i < j → j < cs.length → cs[i]! ≤ cs[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alphabetic (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_alphabetic :
  alphabetic "" = true :=
sorry

theorem single_char_alphabetic (c : Char) :
  alphabetic (String.singleton c) = true :=
sorry

theorem alphabetic_iff_sorted (s : String) :
  alphabetic s = true ↔ isSorted s.data :=
sorry

theorem alphabetic_monotonic (s : String) :
  alphabetic s = true →
  ∀ i : Nat, i + 1 < s.length →
  s.data[i]! ≤ s.data[i+1]! :=
sorry

theorem concat_nonalpha_equiv_sorted (ss : List String) (h : ss ≠ []) :
  (∀ s ∈ ss, alphabetic s = false) →
  alphabetic (String.join ss) = true ↔ isSorted (String.join ss).data :=
sorry
-- </vc-theorems>