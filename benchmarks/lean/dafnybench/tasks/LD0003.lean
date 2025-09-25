-- <vc-preamble>
inductive Unary where
| Zero : Unary
| Suc : Unary → Unary
deriving Repr
def UnaryToNat : Unary → Nat
| Unary.Zero => 0
| Unary.Suc n => 1 + UnaryToNat n
def NatToUnary : Nat → Unary
| 0 => Unary.Zero
| n + 1 => Unary.Suc (NatToUnary n)
def Less : Unary → Unary → Prop
| _, Unary.Zero => False
| Unary.Zero, Unary.Suc _ => True
| Unary.Suc x, Unary.Suc y => Less x y
def LessAlt : Unary → Unary → Prop
| _, Unary.Zero => False
| Unary.Zero, Unary.Suc _ => True
| Unary.Suc x, Unary.Suc y => Less x y
def Add_ : Unary → Unary → Unary
| x, Unary.Zero => x
| x, Unary.Suc y => Unary.Suc (Add_ x y)
def Sub_ : Unary → Unary → Unary
| x, Unary.Zero => x
| Unary.Suc x, Unary.Suc y => Sub_ x y
| Unary.Zero, Unary.Suc _ => Unary.Zero /- This case shouldn't happen given precondition -/
def Mul_ : Unary → Unary → Unary
| Unary.Zero, _ => Unary.Zero
| Unary.Suc x, y => Add_ (Mul_ x y) y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IterativeDivMod (x y : Unary) : Unary × Unary :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IterativeDivMod_spec (x y : Unary) :
y ≠ Unary.Zero →
let (d, m) := IterativeDivMod x y
Add_ (Mul_ d y) m = x ∧ Less m y :=
sorry
-- </vc-theorems>