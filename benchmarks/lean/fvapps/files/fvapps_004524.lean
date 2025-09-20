-- <vc-preamble>
def add : Int → Int → Int := fun a b => a + b

def sub : Int → Int → Int := fun a b => a - b

def mul : Int → Int → Int := fun a b => a * b

def div : Int → Int → Int := fun a b => a / b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def x : List Int → Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem placeholder_identity (args : List Int) (h : args.length > 0) :
  x args = args.head! := by
sorry

theorem placeholder_binary_ops_forward (a b : Int) :
  (add (x [a]) b) = add a b ∧
  (sub (x [a]) b) = sub a b ∧
  (mul (x [a]) b) = mul a b := by
sorry

theorem placeholder_binary_ops_reverse (a b : Int) :
  add b (x [a]) = add b a ∧
  sub b (x [a]) = sub b a ∧
  mul b (x [a]) = mul b a := by
sorry

theorem placeholder_binary_ops_div (a b : Int) :
  b ≠ 0 → div (x [a]) b = div a b := by
sorry

theorem placeholder_binary_ops_div_reverse (a b : Int) :
  a ≠ 0 → div b (x [a]) = div b a := by
sorry

theorem placeholder_chaining (args : List Int) (h : args.length > 1) :
  add (x [args.head!]) (x [args.tail.head!]) = add args.head! args.tail.head! ∧
  mul (x [args.head!]) (x [args.tail.head!]) = mul args.head! args.tail.head! ∧
  add (x [args.head!]) (mul 2 (x [args.tail.head!])) = add args.head! (mul 2 args.tail.head!) := by
sorry

theorem placeholder_constant_folding (a : Int) :
  add (add 2 3) (x [a]) = add 5 a ∧
  add (mul 2 3) (x [a]) = add 6 a := by
sorry
-- </vc-theorems>