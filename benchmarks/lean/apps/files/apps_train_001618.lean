-- <vc-helpers>
-- </vc-helpers>

def rev (s : String) : Nat := sorry 
def solve (s1 s2 : String) : Nat := sorry

theorem solve_commutativity {a b : Nat} :
  solve (toString a) (toString b) = solve (toString b) (toString a) := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible