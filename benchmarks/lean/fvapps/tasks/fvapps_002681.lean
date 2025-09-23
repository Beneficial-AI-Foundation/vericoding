-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def duplicate_encode (s : String) : String := sorry

theorem length_preservation (s : String) : 
  String.length (duplicate_encode s) = String.length s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_output_chars (s : String) (i : String.Pos) :
  (duplicate_encode s).get i = '(' ∨ 
  (duplicate_encode s).get i = ')' := sorry

theorem case_insensitive (s : String) (i : String.Pos) :
  let lower := s.toLower
  let c := lower.get i
  let count := String.toList lower
    |> List.filter (fun x => x = c)
    |> List.length
  (duplicate_encode s).get i = 
    if count = 1 then '(' else ')' := sorry

theorem single_char (s : String) :
  String.length s = 1 →
  duplicate_encode s = "(" := sorry

theorem all_same_chars (s : String) :
  String.length s ≥ 2 →
  (∀ i j : String.Pos, s.get i = s.get j) →
  duplicate_encode s = String.mk (List.replicate (String.length s) ')') := sorry
-- </vc-theorems>