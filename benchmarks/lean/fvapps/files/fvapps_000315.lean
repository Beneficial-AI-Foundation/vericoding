-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_interleave (s1 s2 s3 : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem concat_is_interleave (s1 s2 : String) :
  is_interleave s1 s2 (s1 ++ s2) = true :=
sorry

theorem length_property (s1 s2 s3 : String) :
  s3.length ≠ s1.length + s2.length →
  is_interleave s1 s2 s3 = false :=
sorry

theorem empty_string_interleave (s : String) :
  is_interleave s "" s = true ∧ is_interleave "" s s = true :=
sorry

theorem concat_order_preservation (s1 s2 : String) :
  is_interleave s1 s2 (s1 ++ s2) = true :=
sorry

theorem interleave_commutative (s1 s2 s3 : String) :
  is_interleave s1 s2 s3 = is_interleave s2 s1 s3 :=
sorry

theorem invalid_chars (s1 s2 s3 : String) (c : Char) :
  c ∈ s3.data →
  c ∉ s1.data →
  c ∉ s2.data →
  is_interleave s1 s2 s3 = false :=
sorry
-- </vc-theorems>