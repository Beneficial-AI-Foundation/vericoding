-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mirrorReflection (p q : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mirror_reflection_range (p q : Nat) (hp : p > 0) (hq : q > 0) :
  let r := mirrorReflection p q
  r = 0 ∨ r = 1 ∨ r = 2 :=
sorry

theorem mirror_reflection_reduction (p q : Nat) (hp : p > 0) (hq : q > 0) :
  let p2 := p
  let q2 := q
  mirrorReflection p q = mirrorReflection p2 q2 :=
sorry

theorem mirror_reflection_even_odd (n : Nat) (hn : n > 0) :
  mirrorReflection (2*n) (2*n-1) = 2 :=
sorry

theorem mirror_reflection_odd_even (n : Nat) (hn : n > 0) :
  mirrorReflection (2*n-1) (2*n) = 0 :=
sorry

theorem mirror_reflection_both_odd (n : Nat) (hn : n > 0) :
  mirrorReflection (2*n-1) (2*n-1) = 1 :=
sorry
-- </vc-theorems>