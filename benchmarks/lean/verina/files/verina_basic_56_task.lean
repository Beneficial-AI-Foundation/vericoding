-- <vc-preamble>
@[reducible, simp]
def copy_precond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  src.size ≥ sStart + len ∧
  dest.size ≥ dStart + len
-- </vc-preamble>

-- <vc-helpers>
def updateSegment : Array Int → Array Int → Nat → Nat → Nat → Array Int
  | r, src, sStart, dStart, 0 => r
  | r, src, sStart, dStart, n+1 =>
      let rNew := r.set! (dStart + n) (src[sStart + n]!)
      updateSegment rNew src sStart dStart n
-- </vc-helpers>

-- <vc-definitions>
def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def copy_postcond (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) (result: Array Int) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :=
  result.size = dest.size ∧
  (∀ i, i < dStart → result[i]! = dest[i]!) ∧
  (∀ i, dStart + len ≤ i → i < result.size → result[i]! = dest[i]!) ∧
  (∀ i, i < len → result[dStart + i]! = src[sStart + i]!)

theorem copy_spec_satisfied (src: Array Int) (sStart: Nat) (dest: Array Int) (dStart: Nat) (len: Nat) (h_precond : copy_precond (src) (sStart) (dest) (dStart) (len)) :
    copy_postcond (src) (sStart) (dest) (dStart) (len) (copy (src) (sStart) (dest) (dStart) (len) h_precond) h_precond := by
  sorry
-- </vc-theorems>