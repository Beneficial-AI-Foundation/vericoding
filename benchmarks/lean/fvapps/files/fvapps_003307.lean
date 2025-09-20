-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def time_convert (minutes : Int) : String := sorry

theorem time_convert_output_format {minutes : Int}
  (h1 : -1000 ≤ minutes) (h2 : minutes ≤ 10000) :
  ∃ pre post : String,
    (time_convert minutes = pre ++ ":" ++ post) ∧
    (∀ c ∈ pre.data, c.isDigit) ∧
    (∀ c ∈ post.data, c.isDigit) ∧
    post.length = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem time_convert_zero_or_negative {minutes : Int}
  (h1 : -1000 ≤ minutes) (h2 : minutes ≤ 0) :
  time_convert minutes = "00:00" := sorry

theorem time_convert_properties {minutes : Int}
  (h1 : 1 ≤ minutes) (h2 : minutes ≤ 10000) :
  ∃ hours mins : Nat,
    (time_convert minutes = toString hours ++ ":" ++ toString mins) ∧
    hours * 60 + mins = minutes ∧
    mins < 60 := sorry
-- </vc-theorems>