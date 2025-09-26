-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def de_nico (key : String) (msg : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem de_nico_length_bounded (key : String) (msg : String) :
  (de_nico key msg).length ≤ msg.length := by
  sorry

theorem de_nico_chars_subset (key : String) (msg : String) (c : Char) :
  c ∈ (de_nico key msg).data → c ∈ msg.data := by
  sorry

theorem de_nico_deterministic (key : String) (msg : String) :
  de_nico key msg = de_nico key msg := by
  sorry

theorem de_nico_empty_msg (key : String) :  
  de_nico key "" = "" := by
  sorry

theorem de_nico_no_trailing_spaces (key : String) (msg : String) :
  String.trimRight (de_nico key msg) = de_nico key msg := by
  sorry
-- </vc-theorems>