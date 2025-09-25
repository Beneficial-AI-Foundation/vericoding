-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_isomorphic (s1 s2 : List Char) : Bool :=
  sorry

def unique_chars (s : List Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isomorphic_same_length {s1 s2 : List Char} :
  s1.length ≠ s2.length → ¬is_isomorphic s1 s2 :=
sorry

theorem isomorphic_identical_strings {s : List Char} :
  is_isomorphic s s :=
sorry

theorem isomorphic_reversible {s1 s2 : List Char} :
  s1.length = s2.length →
  is_isomorphic s1 s2 = is_isomorphic s2 s1 :=
sorry

theorem isomorphic_preserves_uniqueness {s1 s2 : List Char} :
  s1.length = s2.length →
  is_isomorphic s1 s2 →
  unique_chars s1 = unique_chars s2 :=
sorry

theorem isomorphic_repeated_chars {s1 s2 : List Char} :
  s1.length = s2.length →
  s1.length ≥ 2 →
  unique_chars s1 = 1 →
  (is_isomorphic s1 s2 ↔ unique_chars s2 = 1) :=
sorry
-- </vc-theorems>