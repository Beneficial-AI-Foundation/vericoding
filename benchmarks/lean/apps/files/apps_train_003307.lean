/-
This kata requires you to convert minutes (`int`) to hours and minutes in the format `hh:mm` (`string`).

If the input is `0` or negative value, then you should return `"00:00"`

**Hint:** use the modulo operation to solve this challenge. The modulo operation simply returns the remainder after a division. For example the remainder of 5 / 2 is 1, so 5 modulo 2 is 1.

## Example

If the input is `78`, then you should return `"01:18"`, because 78 minutes converts to 1 hour and 18 minutes.

Good luck! :D
-/

-- <vc-helpers>
-- </vc-helpers>

def time_convert (minutes : Int) : String := sorry

theorem time_convert_output_format {minutes : Int}
  (h1 : -1000 ≤ minutes) (h2 : minutes ≤ 10000) :
  ∃ pre post : String,
    (time_convert minutes = pre ++ ":" ++ post) ∧
    (∀ c ∈ pre.data, c.isDigit) ∧
    (∀ c ∈ post.data, c.isDigit) ∧
    post.length = 2 := sorry

theorem time_convert_zero_or_negative {minutes : Int}
  (h1 : -1000 ≤ minutes) (h2 : minutes ≤ 0) :
  time_convert minutes = "00:00" := sorry

theorem time_convert_properties {minutes : Int}
  (h1 : 1 ≤ minutes) (h2 : minutes ≤ 10000) :
  ∃ hours mins : Nat,
    (time_convert minutes = toString hours ++ ":" ++ toString mins) ∧
    hours * 60 + mins = minutes ∧
    mins < 60 := sorry

/-
info: '00:00'
-/
-- #guard_msgs in
-- #eval time_convert 0

/-
info: '01:18'
-/
-- #guard_msgs in
-- #eval time_convert 78

/-
info: '16:10'
-/
-- #guard_msgs in
-- #eval time_convert 970

-- Apps difficulty: introductory
-- Assurance level: unguarded