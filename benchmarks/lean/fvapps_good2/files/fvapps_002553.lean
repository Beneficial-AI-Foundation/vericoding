-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.isAlpha : Char → Bool :=
  sorry

def changer : String → String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem changer_length (s : String) :
  s.length = (changer s).length :=
sorry

theorem changer_nonalpha_unchanged {s : String} {i : String.Pos} {c : Char} :
  c = s.get i → ¬(String.isAlpha c) → (changer s).get i = c :=
sorry

theorem changer_empty :
  changer "" = "" :=
sorry

theorem changer_boundary_case :
  changer "abcxyz" = "bcdyzA" :=
sorry
-- </vc-theorems>