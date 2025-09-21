-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def copy (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem copy_spec
(src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) :
src.size ≥ sStart + len →
dest.size ≥ dStart + len →
let r := copy src sStart dest dStart len
(r.size = dest.size) ∧
(∀ i, i < dStart → r[i]! = dest[i]!) ∧
(∀ i, i ≥ dStart + len → r[i]!   = dest[i]!) ∧
(∀ i, dStart ≤ i ∧ i < dStart + len →
r[i]! = src[sStart + (i - dStart)]!) :=
sorry
-- </vc-theorems>