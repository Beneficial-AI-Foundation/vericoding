-- <vc-preamble>
def has_subpattern (s : String) : Bool :=
  sorry

def gcd (a b : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reduce (f : Nat → Nat → Nat) (xs : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_string_property (s : String) :
  (s.length > 1 ∧ s.data.eraseDups.length = 1) → has_subpattern s
  ∧ 
  (s.length = 1) → ¬has_subpattern s :=
  sorry

theorem repeat_property (s : String) :
  s.length ≥ 2 →
  has_subpattern s → 
  has_subpattern (s ++ s) ∧ has_subpattern (s ++ s ++ s) :=
  sorry
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible