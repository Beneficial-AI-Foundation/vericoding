-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s1 s2 : String) : Nat :=
  sorry

def countChar (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_valid_output (s1 s2 : String)
    (h1 : s1.length > 0) (h2 : s2.length > 0) :
  solve s1 s2 = 1 ∨ solve s1 s2 = 2 :=
sorry

theorem solve_identical_chars (s1 s2 : String)
    (h1 : s1.length > 0) (h2 : s2.length > 0)
    (h3 : ∀ (c : Char), s1.data.contains c → c = 'a')
    (h4 : ∀ (c : Char), s2.data.contains c → c = 'a') :
  solve s1 s2 = 2 :=
sorry

theorem solve_with_duplicates (s : String)
    (h1 : s.length ≥ 2) :
  (∃ (c : Char), s.data.contains c ∧ countChar s c ≥ 2) → solve s "" = 1 ∧
  (∀ (c : Char), s.data.contains c → countChar s c < 2) → solve s "" = 2 :=
sorry
-- </vc-theorems>