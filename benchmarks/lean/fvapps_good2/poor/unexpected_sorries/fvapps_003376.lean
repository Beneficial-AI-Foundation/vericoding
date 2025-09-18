def ski_jump (mountain: List String) : String := sorry

def isValidMessage (msg: String) : Bool :=
  msg = "He's crap!" || msg = "He's ok!" || msg = "He's flying!" || msg = "Gold!!"

def stringToFloat (s: String) : Float := sorry -- helper function

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

-- Apps difficulty: introductory
-- Assurance level: guarded

/-
info: "1.35 metres: He's crap!"
-/
#guard_msgs in
#eval ski_jump ["*"]

/-
info: "12.15 metres: He's ok!"
-/
#guard_msgs in
#eval ski_jump ["*", "**", "***"]

/-
info: "48.60 metres: He's flying!"
-/
#guard_msgs in
#eval ski_jump ["*", "**", "***", "****", "*****", "******"]