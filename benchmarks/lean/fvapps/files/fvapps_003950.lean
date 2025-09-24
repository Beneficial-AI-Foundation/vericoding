-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uni_total (s : String) : Nat := sorry

theorem uni_total_empty : uni_total "" = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uni_total_single_char (c : Char) : 
  uni_total (String.mk [c]) = c.toNat := sorry

theorem uni_total_split {s : String} (h : s.length ≥ 2) :
  let mid := s.length / 2
  uni_total s = uni_total (s.take mid) + uni_total (s.drop mid) := sorry

theorem uni_total_additivity (s1 s2 : String) :
  uni_total (s1 ++ s2) = uni_total s1 + uni_total s2 := sorry

theorem uni_total_sum_chars (s : String) :
  uni_total s = s.data.foldr (fun c acc => c.toNat + acc) 0 := sorry
-- </vc-theorems>