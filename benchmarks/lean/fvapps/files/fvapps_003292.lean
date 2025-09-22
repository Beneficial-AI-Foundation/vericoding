-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scramble (s1 s2 : String) : Bool :=
  sorry

def countChar (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scramble_length_property (s1 s2 : String) :
  s1.length > 0 → s2.length > 0 → scramble s1 s2 = true → s1.length ≥ s2.length :=
sorry

theorem scramble_identical_strings (s : String) :
  s.length > 0 → scramble s s = true :=
sorry

theorem scramble_subset_property (s1 s2 : String) (c : Char) :
  s1.length > 0 → s2.length > 0 → scramble s1 s2 = true →
  (countChar s2 c) ≤ (countChar s1 c) :=
sorry

theorem scramble_empty_second_string (s : String) :
  s.length > 0 → scramble s "" = true :=
sorry

theorem scramble_empty_first_string (c : Char) :
  scramble "" (String.singleton c) = false :=
sorry

theorem scramble_disjoint_alphabets (s1 s2 : String) :
  s1.length > 0 → s2.length > 0 →
  (∀ c, s1.contains c → ¬s2.contains c) →
  scramble s1 s2 = false :=
sorry
-- </vc-theorems>