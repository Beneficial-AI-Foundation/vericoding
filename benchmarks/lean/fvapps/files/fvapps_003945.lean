-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>