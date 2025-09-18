-- <vc-preamble>
def check_root (s : String) : String := sorry

def sqrt (n : Nat) : Nat := sorry

def is_consecutive (a b c d : Int) : Bool := 
  b = a + 1 ∧ c = b + 1 ∧ d = c + 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countChar (s : String) (c : Char) : Nat := sorry

theorem invalid_input (s : String) 
  (h : s.isEmpty ∨ 
       (countChar s ',' ≠ 3) ∨ 
       ¬(s.split (fun x => x = ',') |>.all (fun n => n.all (fun c => c.isDigit ∨ c = '-')))) :
  check_root s = "incorrect input" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem consecutive_valid {a b c d : Int} (h : is_consecutive a b c d) :
  check_root s!"{a},{b},{c},{d}" = 
    let prod := a * b * c * d + 1
    s!"{prod}, {sqrt prod.toNat}" := sorry

theorem non_consecutive {a b c d : Int} (h : ¬is_consecutive a b c d) :
  check_root s!"{a},{b},{c},{d}" = "not consecutive" := sorry
-- </vc-theorems>