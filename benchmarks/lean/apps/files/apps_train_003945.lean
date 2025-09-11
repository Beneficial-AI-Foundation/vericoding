-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_percentage (sent : Int) (limit : Int := 1000) : String := sorry

theorem get_percentage_within_limits {sent : Int} 
  (h1 : 1 ≤ sent) (h2 : sent ≤ 999) :
  let result := get_percentage sent
  (result.endsWith "%") ∧
  let percent := (result.dropRight 1).toInt!
  0 ≤ percent ∧ percent ≤ 100 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem limit_exceeded {sent : Int}
  (h : 1000 ≤ sent) :
  get_percentage sent = "Daily limit is reached" := sorry

theorem custom_limit {sent limit : Int}
  (h1 : 1 ≤ sent) (h2 : 1 ≤ limit) :
  let result := get_percentage sent limit
  if sent ≥ limit then
    result = "Daily limit is reached"
  else
    (result.endsWith "%") ∧
    let percent := (result.dropRight 1).toInt!
    0 ≤ percent ∧ percent ≤ 100 := sorry

theorem zero_emails :
  get_percentage 0 = "No e-mails sent" := sorry

/-
info: '10%'
-/
-- #guard_msgs in
-- #eval get_percentage 101 1000

/-
info: '51%'
-/
-- #guard_msgs in
-- #eval get_percentage 256 500

/-
info: '25%'
-/
-- #guard_msgs in
-- #eval get_percentage 259

/-
info: 'No e-mails sent'
-/
-- #guard_msgs in
-- #eval get_percentage 0

/-
info: 'Daily limit is reached'
-/
-- #guard_msgs in
-- #eval get_percentage 1000 1000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded