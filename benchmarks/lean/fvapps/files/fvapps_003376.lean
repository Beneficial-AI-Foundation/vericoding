-- <vc-preamble>
def isValidMessage (msg: String) : Bool :=
  msg = "He's crap!" || msg = "He's ok!" || msg = "He's flying!" || msg = "Gold!!"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ski_jump (mountain: List String) : String := 
  sorry

def stringToFloat (s: String) : Float := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ski_jump_output_format {mountain : List String} (h : mountain.length > 0) :
  let result := ski_jump mountain
  let parts := result.splitOn " metres: "
  parts.length = 2 ∧
  (let number := parts[0]!
   let message := parts[1]!
   stringToFloat number ≥ 0 ∧
   isValidMessage message) :=
sorry

theorem jump_length_proportional_to_height {mountain : List String} (h : mountain.length > 0) :
  let result := ski_jump mountain
  let jumpLength := stringToFloat (result.splitOn " metres: ")[0]!
  jumpLength = Float.ofNat mountain.length * (Float.ofNat mountain.length * 1.5) * 0.9 :=
sorry

theorem message_thresholds {mountain : List String} (h : mountain.length > 0) :
  let result := ski_jump mountain
  let length := stringToFloat (result.splitOn " metres: ")[0]!
  let message := (result.splitOn "metres: ")[1]!
  (length < 10 → message = "He's crap!") ∧
  (length ≥ 10 ∧ length < 25 → message = "He's ok!") ∧
  (length ≥ 25 ∧ length < 50 → message = "He's flying!") ∧
  (length ≥ 50 → message = "Gold!!") :=
sorry
-- </vc-theorems>