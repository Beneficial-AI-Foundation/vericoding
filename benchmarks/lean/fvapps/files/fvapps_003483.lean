-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def domino_reaction (s : String) : String := sorry

theorem domino_reaction_length (s : String) : 
  (domino_reaction s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem domino_reaction_preserves_non_vertical (s : String) (i : String.Pos) : 
  s.get i ≠ '|' → 
  (domino_reaction s).get i = s.get i := sorry

theorem domino_reaction_preserves_after_non_vertical (s : String) (i : String.Pos) 
  (j : String.Pos) :
  s.get i ≠ '|' →
  i ≤ j →
  (domino_reaction s).get j = s.get j := sorry

theorem domino_reaction_valid_chars (s : String) :
  ∀ c, c ∈ (domino_reaction s).data → 
  c = '|' ∨ c = '/' ∨ c = ' ' := sorry 

theorem domino_reaction_idempotent (s : String) :
  domino_reaction (domino_reaction s) = domino_reaction s := sorry
-- </vc-theorems>