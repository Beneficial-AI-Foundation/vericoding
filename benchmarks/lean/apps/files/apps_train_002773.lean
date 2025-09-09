-- <vc-helpers>
-- </vc-helpers>

def x (n: Nat): String := sorry

def nthChar (s: String) (i: Nat) : Char :=
  s.get ⟨i⟩

theorem x_correct_dimensions {n: Nat} (h: n > 0): 
  let lines := (x n).split (· = '\n')
  lines.length = n ∧ 
  lines.all (fun line => line.length = n) := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible