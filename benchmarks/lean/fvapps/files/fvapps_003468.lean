-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def my_crib (n : Nat) : String := sorry

def splitLines (s : String) : List String :=
  s.splitOn "\n"
-- </vc-definitions>

-- <vc-theorems>
theorem crib_line_count (n : Nat) (h : 0 < n) :
  (splitLines (my_crib n)).length = 2 * n + 1 := sorry

theorem crib_roof_chars (n : Nat) (h : 0 < n) (i : Nat) (h2 : i < n) 
    (h3 : i < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[i]'h3
  line.trim.data.get? 0 = some '/' ∧ 
  line.trim.data.getLast? = some '\\' := sorry

theorem crib_ceiling_chars (n : Nat) (h : 0 < n) 
    (h2 : n < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[n]'h2
  line.data.get? 0 = some '/' ∧ 
  line.data.getLast? = some '\\' := sorry

theorem crib_wall_chars (n : Nat) (h : 0 < n) (i : Nat) 
    (h2 : n + 1 ≤ i) (h3 : i < 2*n)
    (h4 : i < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[i]'h4
  line.data.get? 0 = some '|' ∧ 
  line.data.getLast? = some '|' := sorry

theorem crib_floor_chars (n : Nat) (h : 0 < n)
    (h2 : 2*n < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[2*n]'h2
  line.data.get? 0 = some '|' ∧ 
  line.data.getLast? = some '|' := sorry

theorem crib_line_widths (n : Nat) (h : 0 < n)
    (i j : Nat) (hi : i < (splitLines (my_crib n)).length) 
    (hj : j < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  (lines[i]'hi).data.length = (lines[j]'hj).data.length ∧
  (lines[i]'hi).data.length = 2*n + 2 := sorry

theorem crib_underscore_count (n : Nat) (h : 0 < n)
    (h2 : n < (splitLines (my_crib n)).length)
    (h3 : 2*n < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let ceiling := lines[n]'h2
  let floor := lines[2*n]'h3
  (List.filter (· = '_') ceiling.data).length = 2*n ∧
  (List.filter (· = '_') floor.data).length = 2*n := sorry

theorem crib_symmetry (n : Nat) (h : 0 < n) 
    (i : Nat) (h2 : i < (splitLines (my_crib n)).length) :
  let lines := splitLines (my_crib n)
  let line := lines[i]'h2
  ∃ s : List Char,
    s = line.data ∧
    s = (s.reverse.map (fun c => 
      if c = '\\' then '/' 
      else if c = '/' then '\\'
      else c)) := sorry
-- </vc-theorems>