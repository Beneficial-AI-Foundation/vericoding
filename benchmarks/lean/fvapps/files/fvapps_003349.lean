-- <vc-preamble>
def calculate_seconds (time_str : String) : Nat :=
  sorry

def longest_possible (seconds : Int) : Option String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def song_durations : List String :=
  ["03:36", "06:48", "04:27", "03:50", "04:32", "04:22", "03:30", "03:25", "04:34"]
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_seconds_basic_properties {minutes seconds : Nat} 
  (h1 : minutes ≤ 59) (h2 : seconds ≤ 59) : 
  (calculate_seconds s!"{minutes}:{seconds}" = minutes * 60 + seconds) ∧ 
  (calculate_seconds s!"{minutes}:{seconds}" ≥ 0) :=
sorry

theorem longest_possible_properties (seconds : Int) :
  match longest_possible seconds with
  | some result => 
    result ∈ song_durations ∧
    calculate_seconds result ≤ seconds ∧
    ∀ s ∈ song_durations, 
      calculate_seconds s ≤ seconds → 
      calculate_seconds s ≤ calculate_seconds result
  | none =>
    ∀ duration ∈ song_durations, 
      calculate_seconds duration > seconds :=
sorry

/-
info: 'For Reasons Unknown'
-/
-- #guard_msgs in
-- #eval longest_possible 215

/-
info: 'YYZ'
-/
-- #guard_msgs in
-- #eval longest_possible 270

/-
info: False
-/
-- #guard_msgs in
-- #eval longest_possible 13

/-
info: 'Surfing With The Alien'
-/
-- #guard_msgs in
-- #eval longest_possible 300
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded