-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def valid_time_str (h : Nat) (m : Nat) (s : Nat) : String := sorry

def find_thief_with_watch (times : List String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_thief_returns_valid_index 
  (times : List String) 
  (h_nonempty : times ≠ []) :
  let result := find_thief_with_watch times
  1 ≤ result ∧ result ≤ times.length := sorry

theorem find_thief_handles_modulo
  (times : List String)
  (h_nonempty : times ≠ []) :
  let times_with_large := times ++ ["25:30:45"]
  let result1 := find_thief_with_watch times
  let result2 := find_thief_with_watch times_with_large
  result2 ≤ times.length → result1 = result2 := sorry

theorem find_thief_single_time
  (h : Nat)
  (h_valid : h ≤ 23) :
  let time := [valid_time_str h 0 0] 
  find_thief_with_watch time = 1 := sorry

theorem find_thief_same_minute_second
  (hours : List Nat)
  (h_nonempty : hours ≠ [])
  (h_valid : ∀ h ∈ hours, h ≤ 23) :
  let times := hours.map (fun h => valid_time_str h 30 30)
  let result := find_thief_with_watch times
  1 ≤ result ∧ result ≤ times.length := sorry
-- </vc-theorems>