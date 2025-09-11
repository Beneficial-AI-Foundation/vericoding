-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_matched : List String → String ⊕ Bool
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_matched_output_type (cigar seq : String) :
  match is_matched [cigar, seq] with
  | Sum.inl _ => True 
  | Sum.inr b => b = true ∨ b = false
  := sorry

theorem exact_match_works (n : Nat) (seq : String) :
  seq.length = n →
  is_matched [s!"{n}M", seq] = Sum.inr true
  := sorry

theorem invalid_length_implies_error (cigar seq : String) :
  let totalOps := sorry -- Sum of numbers in cigar string
  seq.length ≠ totalOps →
  ¬cigar.endsWith "M" →
  is_matched [cigar, seq] = Sum.inl "Invalid cigar"
  := sorry

theorem single_M_matches_exact (seq : String) :
  is_matched [s!"{seq.length}M", seq] = Sum.inr true
  := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_matched ["36M", "CATAATACTTTACCTACTCTCAACAAATGCGGGAGA"]

/-
info: 'Invalid cigar'
-/
-- #guard_msgs in
-- #eval is_matched ["10M6H", "GAGCGAGTGCGCCTTAC"]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_matched ["12S", "TGTTTCTCCAAG"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded