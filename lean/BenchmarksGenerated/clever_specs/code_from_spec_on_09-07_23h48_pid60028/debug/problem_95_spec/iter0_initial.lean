def problem_spec
-- function signature
(implementation: Std.HashMap String String → Bool)
-- inputs
(D: Std.HashMap String String) :=
-- spec
let spec (result : Bool) :=
  match D.isEmpty with
  | true => result = false
  | false =>
    let keys := D.keys
    let all_lower := keys.all (fun s => s.toLower = s)
    let all_upper := keys.all (fun s => s.toUpper = s)
    result = true ↔ all_lower || all_upper
-- program termination
∃ result,
  implementation D = result ∧
  spec result

def implementation (D: Std.HashMap String String) : Bool :=
  if D.isEmpty then
    false
  else
    let keys := D.keys
    let all_lower := keys.all (fun s => s.toLower = s)
    let all_upper := keys.all (fun s => s.toUpper = s)
    all_lower || all_upper

theorem correctness
(D: Std.HashMap String String)
: problem_spec implementation D := by
  unfold problem_spec
  exists implementation D
  constructor
  · rfl
  · unfold implementation
    simp only [ite_true]
    split
    · rfl
    · simp only [Bool.true_iff]