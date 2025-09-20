-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def summy (s : String) : Int :=
sorry

def sum (l : List Int) : Int :=
sorry

def stringToList (s : String) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem summy_matches_direct_sum (l : List Int) (h : l.length > 0) :
  summy (String.intercalate " " (List.map toString l)) = sum l :=
sorry

theorem summy_handles_whitespace (l : List Int) (h : l.length > 0) :
  summy (String.intercalate "   " (List.map toString l)) = sum l :=
sorry
-- </vc-theorems>