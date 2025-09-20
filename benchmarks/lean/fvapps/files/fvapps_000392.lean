-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Point := Nat × Nat

def is_escape_possible (blocked : List Point) (source target : Point) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_blocked_always_possible (source target : Point) :
  is_escape_possible [] source target = true := sorry

theorem blocked_source_target_impossible {blocked : List Point} {source target : Point} :
  (source ∈ blocked ∨ target ∈ blocked) →
  is_escape_possible blocked source target = false := sorry

theorem same_source_target_possible {blocked : List Point} {source : Point} :
  source ∉ blocked →
  is_escape_possible blocked source source = true := sorry

theorem symmetry {blocked : List Point} {source target : Point} :
  is_escape_possible blocked source target = is_escape_possible blocked target source := sorry

theorem adjacent_points_blocked {source : Point} 
    (x := source.1)
    (y := source.2)
    (blocked := [(x+1,y), (x-1,y), (x,y+1), (x,y-1)])
    (target := (x+2, y+2)) :
  is_escape_possible blocked source target = false := sorry
-- </vc-theorems>