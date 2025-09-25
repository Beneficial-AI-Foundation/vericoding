-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def camel_case (s : String) : String := sorry

theorem camel_case_no_spaces (s : String) : 
  ∀ (i : String.Pos), (camel_case s).get i ≠ ' ' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem camel_case_preserves_length (s : String) :
  String.length (camel_case s) = String.length (s.replace " " "") := sorry

theorem camel_case_single_word (s : String) (h : s ≠ "") :
  match (camel_case s).get? 0, s.get? 0 with
  | some c₁, some c₂ => c₁ = Char.toUpper c₂
  | _, _ => True
  := sorry

theorem camel_case_only_spaces (s : String) 
  (h : ∀ (i : String.Pos), s.get i = ' ') :
  camel_case s = "" := sorry
-- </vc-theorems>