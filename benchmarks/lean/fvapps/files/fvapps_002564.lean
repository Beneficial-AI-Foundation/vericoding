-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solution (s : String) : String := sorry

theorem uppercase_preceded_by_space (s : String) (pos : String.Pos) :
  pos < s.endPos →
  (s.get pos).isUpper →
  let res := solution s
  ∃ resPos : String.Pos, 
    res.get resPos = s.get pos ∧ 
    (∃ prevPos : String.Pos, 
      prevPos < resPos ∧
      res.get prevPos = ' ') := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_difference_equals_uppercase_count (s : String) :
  (solution s).length = s.length + (s.data.filter Char.isUpper).length := sorry

theorem lowercase_unchanged (s : String) :
  s.data.all (fun c => !c.isUpper) →
  solution s = s := sorry
-- </vc-theorems>