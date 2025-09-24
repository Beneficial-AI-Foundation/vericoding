-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ones_complement (s: String) : String := sorry

theorem ones_complement_double_complement (s: String) :
  ones_complement (ones_complement s) = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ones_complement_length_preservation (s: String) :
  (ones_complement s).length = s.length := sorry

theorem ones_complement_valid_output (s: String) (i: String.Pos) :
  ((ones_complement s).get i = '0' ∨ (ones_complement s).get i = '1') := sorry

theorem ones_complement_flips_bits (s: String) (i: String.Pos) :
  (ones_complement s).get i ≠ s.get i := sorry

theorem ones_complement_empty :
  ones_complement "" = "" := sorry
-- </vc-theorems>