-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greatest (x y n : Nat) : Nat :=
  sorry

def smallest (x y n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divisible_by_inputs {x y n : Nat} (hx : x > 0) (hy : y > 0) :
  let g := greatest x y (max x y * 2)
  let s := smallest x y (max x y * 2)
  g % x = 0 ∧ g % y = 0 ∧ s % x = 0 ∧ s % y = 0 :=
sorry

theorem bounds {x y n : Nat} (hx : x > 0) (hy : y > 0) (hn : n > 0) :
  let g := greatest x y n
  let s := smallest x y n
  g < n ∧ s > n ∧ s > g :=
sorry
-- </vc-theorems>