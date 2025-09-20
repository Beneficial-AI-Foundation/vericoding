-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.count (s : String) (c : Char) : Nat :=
  sorry

def String.strip (s : String) : String :=
  sorry

def array (s : String) : Option String :=
  sorry

def joinWithSpaces (xs : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_none_when_not_enough_commas (s : String) :
  s.count ',' < 2 →
  array s = none :=
sorry

theorem array_processes_middle_elements (s : String) :
  s.count ',' ≥ 2 →
  array s = some (joinWithSpaces (List.map String.strip (List.drop 1 (List.take (List.length (String.splitOn "," s) - 1) (String.splitOn "," s))))) :=
sorry
-- </vc-theorems>