-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def x (n: Nat): String := sorry

def nthChar (s: String) (i: Nat) : Char :=
  s.get ⟨i⟩
-- </vc-definitions>

-- <vc-theorems>
theorem x_correct_dimensions {n: Nat} (h: n > 0): 
  let lines := (x n).split (· = '\n')
  lines.length = n ∧ 
  lines.all (fun line => line.length = n) := sorry
-- </vc-theorems>