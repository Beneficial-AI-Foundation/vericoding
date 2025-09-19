-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toLoverCase (s : String) : String := sorry
def isAlpha (c : Char) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preserved (s : String) :
  String.length (toLoverCase s) = String.length s := sorry

theorem non_alpha_preserved (s : String) (i : String.Pos) :
  !isAlpha (s.get i) →
  (toLoverCase s).get i = s.get i := sorry

theorem output_only_love_or_unchanged (s : String) (i : String.Pos) :
  let c := (toLoverCase s).get i
  if isAlpha (s.get i)
  then c = 'L' ∨ c = 'O' ∨ c = 'V' ∨ c = 'E'
  else c = s.get i := sorry

theorem consistent_mapping (s : String) (i j : String.Pos) :
  isAlpha (s.get i) →
  s.get i = s.get j →
  (toLoverCase s).get i = (toLoverCase s).get j := sorry
-- </vc-theorems>