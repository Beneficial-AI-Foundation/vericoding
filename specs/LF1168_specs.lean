-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_take_bath (v1 v2 v3 : Nat) (t1 t2 t3 : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_take_bath_t3_between : 
  ∀ (v1 v2 v3 t1 t2 t3 : Nat),
    v1 > 0 → v2 > 0 → v3 > 0 →
    t1 ≤ t2 →
    can_take_bath v1 t1 v2 t2 v3 t3 = true →
    t1 ≤ t3 ∧ t3 ≤ t2 :=
sorry

theorem can_take_bath_outside_false :
  ∀ (v1 v2 v3 t1 t2 t3 : Nat),
    v1 > 0 → v2 > 0 → v3 > 0 →
    t1 ≤ t2 → 
    (¬(t1 ≤ t3 ∧ t3 ≤ t2)) →
    can_take_bath v1 t1 v2 t2 v3 t3 = false :=
sorry

theorem can_take_bath_equal_rates :
  ∀ (v t1 t2 t3 : Nat),
    v > 0 →
    t1 ≤ t3 → t3 ≤ t2 →
    can_take_bath v t1 v t2 v t3 = true :=
sorry
-- </vc-theorems>