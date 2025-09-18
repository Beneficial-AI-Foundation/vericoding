-- <vc-preamble>
def abs (x : Int) : Int := 
  if x < 0 then -x else x

def minimum (lst : List Int) : Option Int := 
  lst.foldl (fun min x => match min with
    | none => some x
    | some m => some (if x < m then x else m)) none
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def closest (lst : List Int) : Option Int := sorry

theorem closest_returns_none_or_element (lst : List Int) (h : lst ≠ []) :
  match closest lst with
  | none => True
  | some x => x ∈ lst
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem closest_zero (lst : List Int) (h : lst ≠ []) :
  0 ∈ lst → closest lst = some 0 := sorry

theorem closest_none_when_equal_absolutes (lst : List Int) (h : lst ≠ []) :
  match closest lst with
  | none => ∃ x ∈ lst, -x ∈ lst
  | some x => (match minimum (lst.map abs) with
              | none => False
              | some m => abs x = m) ∧ -x ∉ lst
  := sorry

theorem closest_is_minimum_absolute (lst : List Int) (h : lst ≠ []) :
  match closest lst with
  | none => True
  | some x => match minimum (lst.map abs) with
              | none => False
              | some m => abs x = m
  := sorry
-- </vc-theorems>