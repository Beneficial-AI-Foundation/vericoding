-- <vc-helpers>
-- </vc-helpers>

def can_take_bath (v1 v2 v3 : Nat) (t1 t2 t3 : Nat) : Bool :=
sorry

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

/-
info: True
-/
-- #guard_msgs in
-- #eval can_take_bath 5 10 5 20 8 15

/-
info: False
-/
-- #guard_msgs in
-- #eval can_take_bath 5 10 5 20 1 30

/-
info: True
-/
-- #guard_msgs in
-- #eval can_take_bath 5 10 5 20 5 20

-- Apps difficulty: interview
-- Assurance level: unguarded