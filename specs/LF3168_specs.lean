-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def func_or (a b : Bool) : Bool := sorry
def func_xor (a b : Bool) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem or_basic (a b : Bool) : 
  func_or a b = (a || b) := sorry

theorem or_commutative (a b : Bool) : 
  func_or a b = func_or b a := sorry

theorem or_identity_true (b : Bool) :
  func_or true b = true := sorry

theorem or_identity_false (b : Bool) :
  func_or false b = b := sorry

theorem xor_basic (a b : Bool) : 
  func_xor a b = (a != b) := sorry

theorem xor_commutative (a b : Bool) :
  func_xor a b = func_xor b a := sorry

theorem xor_same (a : Bool) :
  ¬(func_xor a a) := sorry

theorem xor_double (a b : Bool) :
  func_xor (func_xor a b) b = a := sorry
-- </vc-theorems>