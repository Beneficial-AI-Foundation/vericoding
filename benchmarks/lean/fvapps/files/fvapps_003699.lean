-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shifted_diff (s1 s2 : String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shifted_diff_same_string (s : String) (h : s.length > 0) :
  shifted_diff s s = 0 := 
  sorry

theorem shifted_diff_rotation (s : String) (n : Nat) (h : s.length > 0) :
  let rotated := (s.drop (n % s.length)).append (s.take (n % s.length))
  shifted_diff s rotated ≥ 0 :=
  sorry

theorem shifted_diff_different_lengths (s1 s2 : String) 
  (h1 : s1.length > 0) (h2 : s2.length > 0) (h3 : s1.length ≠ s2.length) :
  shifted_diff s1 s2 = -1 :=
  sorry

theorem shifted_diff_not_rotation (s1 s2 : String)
  (h1 : s1.length > 0) (h2 : s2.length > 0) 
  (h3 : s1.length = s2.length)
  (h4 : s1.data ≠ s2.data) :
  shifted_diff s1 s2 = -1 :=
  sorry
-- </vc-theorems>