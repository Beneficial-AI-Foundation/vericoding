-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_divmod (a b : Int) : Option (Int × Int × (Int × Int)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_divmod_structure (a b : Int) (h : b ≠ 0) :
  ∃ q r t, process_divmod a b = some (q, r, t) := 
  sorry

theorem process_divmod_tuple_match (a b : Int) (h : b ≠ 0) :
  ∀ q r t, process_divmod a b = some (q, r, t) → t = (q, r) :=
  sorry

theorem process_divmod_quotient (a b : Int) (h : b ≠ 0) :
  ∀ q r t, process_divmod a b = some (q, r, t) → q = a / b :=
  sorry

theorem process_divmod_remainder (a b : Int) (h : b ≠ 0) :
  ∀ q r t, process_divmod a b = some (q, r, t) → r = a % b :=
  sorry

theorem process_divmod_zero (a : Int) :
  process_divmod a 0 = none :=
  sorry
-- </vc-theorems>