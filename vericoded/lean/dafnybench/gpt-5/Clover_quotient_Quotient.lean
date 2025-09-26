import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper definitions needed for this file.

-- </vc-helpers>

-- <vc-definitions>
def Quotient_ (x : Nat) (y : Nat) : Int × Int :=
  let r := x % y
  let q := x / y
  (Int.ofNat r, Int.ofNat q)
-- </vc-definitions>

-- <vc-theorems>
theorem Quotient_spec (x : Nat) (y : Nat) :
y ≠ 0 →
let (r, q) := Quotient_ x y
q * y + r = x ∧ 0 ≤ r ∧ r < y ∧ 0 ≤ q :=
by
  intro hy
  have hy_pos : 0 < y := Nat.pos_of_ne_zero hy
  have hnat : (x / y) * y + x % y = x := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div x y)
  have hEq : (Int.ofNat (x / y) : Int) * y + Int.ofNat (x % y) = (x : Int) := by
    simpa [Int.ofNat_add, Int.ofNat_mul] using congrArg Int.ofNat hnat
  have hr_nonneg : 0 ≤ (Int.ofNat (x % y)) := Int.ofNat_nonneg _
  have hr_lt : (Int.ofNat (x % y)) < (y : Int) := (Int.ofNat_lt).mpr (Nat.mod_lt x hy_pos)
  have hq_nonneg : 0 ≤ (Int.ofNat (x / y)) := Int.ofNat_nonneg _
  simpa [Quotient_] using And.intro hEq (And.intro hr_nonneg (And.intro hr_lt hq_nonneg))
-- </vc-theorems>
