-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def catMouse (s : String) : String := sorry

def countDots (s : String) : Nat := 
  s.toList.filter (· = '.') |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem catMouse_output_valid (s : String) 
    (h : ∃ n : Nat, n ≤ 10 ∧ s = "C" ++ (String.mk (List.replicate n '.')) ++ "m") : 
    catMouse s = "Caught!" ∨ catMouse s = "Escaped!" := sorry

theorem catMouse_dots_escape (s : String) 
    (h : ∃ n : Nat, n ≤ 10 ∧ s = "C" ++ (String.mk (List.replicate n '.')) ++ "m") :
    (catMouse s = "Escaped!") ↔ (countDots s > 3) := sorry

theorem catMouse_dots_caught (s : String) 
    (h : ∃ n : Nat, n ≤ 10 ∧ s = "C" ++ (String.mk (List.replicate n '.')) ++ "m") :
    (catMouse s = "Caught!") ↔ (countDots s ≤ 3) := sorry

theorem catMouse_edge_cases : 
    (catMouse "Cm" = "Caught!") ∧ 
    (catMouse "C....m" = "Escaped!") := sorry
-- </vc-theorems>