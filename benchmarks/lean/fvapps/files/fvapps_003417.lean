-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lovefunc (f1 f2 : Int) : Bool := sorry

theorem lovefunc_symmetry (f1 f2 : Int) :
  lovefunc f1 f2 = lovefunc f2 f1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lovefunc_parity (f1 f2 : Int) :
  lovefunc f1 f2 = (f1 % 2 ≠ f2 % 2) := sorry

theorem lovefunc_same_number (x : Int) :
  lovefunc x x = false := sorry

theorem lovefunc_consecutive (x : Int) :
  lovefunc x (x + 1) = true := sorry
-- </vc-theorems>