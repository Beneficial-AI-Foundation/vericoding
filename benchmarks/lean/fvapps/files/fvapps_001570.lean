-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def proper_fractions (n: Nat) : Nat := sorry

def count_coprime_nums (n: Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem proper_fractions_matches_count (n: Nat) (h: n ≥ 1) :
  proper_fractions n = count_coprime_nums n := sorry

theorem proper_fractions_bounds (n: Nat) (h: n ≥ 2) :
  proper_fractions n < n ∧ proper_fractions n ≥ 0 := sorry

theorem proper_fractions_one :
  proper_fractions 1 = 0 := sorry
-- </vc-theorems>