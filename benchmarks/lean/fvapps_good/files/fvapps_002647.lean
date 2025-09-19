-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def time (distance : Nat) (boat_speed : Nat) (stream : String) : Float := sorry

def stream_speed : String → Nat 
  | s => match s.splitOn " " with
    | [_, speed] => (String.toNat! speed)
    | _ => 0
-- </vc-definitions>

-- <vc-theorems>
theorem time_is_positive (distance : Nat) (boat_speed : Nat) (stream : String)  
  (h1 : distance > 0)
  (h2 : boat_speed > 0) 
  (h3 : boat_speed > stream_speed stream) :
  time distance boat_speed stream > 0 := sorry

theorem time_matches_calculation (distance : Nat) (boat_speed : Nat) (stream : String)
  (h1 : distance > 0)
  (h2 : boat_speed > 0)
  (h3 : boat_speed > stream_speed stream) :
  let expected := 
    if stream.startsWith "Downstream" then 
      Float.ofNat distance / Float.ofNat (boat_speed + stream_speed stream)
    else
      Float.ofNat distance / Float.ofNat (boat_speed - stream_speed stream)
  Float.abs (time distance boat_speed stream - expected) < 0.01 := sorry

theorem downstream_faster_than_upstream 
  (distance : Nat) (boat_speed : Nat) (speed : Nat)
  (h1 : distance > 0)
  (h2 : boat_speed > speed)
  (h3 : speed > 0) :
  time distance boat_speed ("Downstream " ++ toString speed) < 
  time distance boat_speed ("Upstream " ++ toString speed) := sorry
-- </vc-theorems>