-- <vc-preamble>
def SWIM_DIST : Float := 2.4
def BIKE_DIST : Float := 112

def RUN_DIST : Float := 26.2
def TOTAL_DIST : Float := SWIM_DIST + BIKE_DIST + RUN_DIST
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def i_tri (distance : Float) : String ⊕ (String × String) := sorry

theorem i_tri_result_type (distance : Float) :
  match i_tri distance with
  | Sum.inl _ => True
  | Sum.inr _ => True := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem i_tri_at_start :
  i_tri 0 = Sum.inl "Starting Line... Good Luck!" := sorry

theorem i_tri_at_finish (distance : Float) :
  distance ≥ TOTAL_DIST →
  i_tri distance = Sum.inl "You're done! Stop running!" := sorry

theorem i_tri_swim_phase (distance : Float) :
  0 < distance → distance < SWIM_DIST → 
  ∃ msg, i_tri distance = Sum.inr ("Swim", msg) := sorry

theorem i_tri_bike_phase (distance : Float) :
  SWIM_DIST ≤ distance → distance < SWIM_DIST + BIKE_DIST →
  ∃ msg, i_tri distance = Sum.inr ("Bike", msg) := sorry

theorem i_tri_run_phase_normal (distance : Float) :
  SWIM_DIST + BIKE_DIST ≤ distance → distance < TOTAL_DIST - 10 →
  ∃ msg, i_tri distance = Sum.inr ("Run", msg) ∧ msg.endsWith " to go!" := sorry

theorem i_tri_run_phase_near_end (distance : Float) :
  TOTAL_DIST - 10 ≤ distance → distance < TOTAL_DIST →
  i_tri distance = Sum.inr ("Run", "Nearly there!") := sorry
-- </vc-theorems>