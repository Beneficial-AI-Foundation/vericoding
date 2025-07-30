def problem_spec
-- function signature
(implementation: List (String × String) → Bool)
-- inputs
(D: List (String × String)) :=
-- spec
let spec (result : Bool) :=
  match D with
  | [] => result = false
  | _ =>
    let keys := D.map (·.1)
    let all_lower := keys.all (fun s => s.toLower = s)
    let all_upper := keys.all (fun s => s.toUpper = s)
    result = true ↔ all_lower || all_upper
-- program termination
∃ result,
  implementation D = result ∧
  spec result

def implementation (D: List (String × String)) : Bool :=
  if D.isEmpty then
    false
  else
    let keys := D.map (·.1)
    let all_lower := keys.all (fun s => s.toLower = s)
    let all_upper := keys.all (fun s => s.toUpper = s)
    all_lower || all_upper

-- LLM HELPER
lemma List.isEmpty_iff_nil {α : Type*} (l: List α) : l.isEmpty = true ↔ l = [] := by
  cases l with
  | nil => simp [List.isEmpty]
  | cons h t => simp [List.isEmpty]

theorem correctness
(D: List (String × String))
: problem_spec implementation D := by
  unfold problem_spec
  exists implementation D
  constructor
  · rfl
  · unfold implementation
    split
    case isTrue h =>
      rw [List.isEmpty_iff_nil] at h
      rw [h]
      simp
    case isFalse h =>
      rw [List.isEmpty_iff_nil] at h
      cases D with
      | nil => simp at h
      | cons x xs => 
        simp
        constructor
        · intro h_impl
          exact h_impl
        · intro h_spec
          exact h_spec