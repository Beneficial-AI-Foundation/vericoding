-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Float.toDegrees (x : Float) : Float :=
  sorry

def Int.toFloat (x : Int) : Float :=
  sorry

def missing_angle (h a o : Float) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem missing_angle_output_range (h a o : Float) :
  h > 0 ∨ a > 0 ∨ o > 0 →
  let angle := missing_angle h a o
  0 ≤ angle ∧ angle ≤ 90 :=
sorry

theorem missing_angle_with_missing_hyp (a o : Float) :
  a > 0 ∧ o > 0 →
  let angle := missing_angle 0 a o
  (Int.toFloat angle - Float.toDegrees ((o/a).atan)).abs ≤ 1 :=
sorry

theorem missing_angle_with_missing_adj (h o : Float) :
  h > 0 ∧ o > 0 →
  let angle := missing_angle h 0 o
  (Int.toFloat angle - Float.toDegrees ((o/h).asin)).abs ≤ 1 :=
sorry

theorem missing_angle_with_missing_opp (h a : Float) :
  h > 0 ∧ a > 0 →
  let angle := missing_angle h a 0
  (Int.toFloat angle - Float.toDegrees ((a/h).acos)).abs ≤ 1 :=
sorry

theorem missing_angle_two_zeros (o : Float) :
  o > 0 →
  ¬∃angle, missing_angle 0 0 o = angle :=
sorry

theorem missing_angle_invalid_triangle (h a : Float) :
  h > 0 ∧ a > 0 →
  a > h →
  ¬∃angle, missing_angle h a 0 = angle :=
sorry
-- </vc-theorems>