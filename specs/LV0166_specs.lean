-- <vc-preamble>
@[reducible, simp]
def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  offset ≥ 0
-- </vc-preamble>

-- <vc-helpers>
def rotateAux (a : Array Int) (offset : Int) (i : Nat) (len : Nat) (b : Array Int) : Array Int :=
  if i < len then
    let idx_int : Int := (Int.ofNat i + offset) % (Int.ofNat len)
    let idx_int_adjusted := if idx_int < 0 then idx_int + Int.ofNat len else idx_int
    let idx_nat : Nat := Int.toNat idx_int_adjusted
    let new_b := b.set! i (a[idx_nat]!)
    rotateAux a offset (i + 1) len new_b
  else b
-- </vc-helpers>

-- <vc-definitions>
def rotate (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def rotate_postcond (a : Array Int) (offset : Int) (result: Array Int) (h_precond : rotate_precond (a) (offset)) :=
  result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)

theorem rotate_spec_satisfied (a: Array Int) (offset: Int) (h_precond : rotate_precond (a) (offset)) :
    rotate_postcond (a) (offset) (rotate (a) (offset) h_precond) h_precond := by
  sorry
-- </vc-theorems>