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
    let keys := D.map (fun p => p.1)
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
    let keys := D.map (fun p => p.1)
    let all_lower := keys.all (fun s => s.toLower = s)
    let all_upper := keys.all (fun s => s.toUpper = s)
    all_lower || all_upper

-- LLM HELPER
lemma implementation_empty (D: List (String × String)) (h: D = []) : implementation D = false := by
  simp [implementation, h]

-- LLM HELPER
lemma implementation_nonempty (D: List (String × String)) (h: D ≠ []) : 
  implementation D = (let keys := D.map (fun p => p.1); let all_lower := keys.all (fun s => s.toLower = s); let all_upper := keys.all (fun s => s.toUpper = s); all_lower || all_upper) := by
  simp [implementation]
  rw [if_neg (List.isEmpty_iff_eq_nil.not.mpr h)]

theorem correctness
(D: List (String × String))
: problem_spec implementation D := by
  simp [problem_spec]
  use implementation D
  constructor
  · rfl
  · cases' D with hd tl
    · simp [implementation]
    · simp [implementation, List.isEmpty_iff_eq_nil]
      let keys := (hd :: tl).map (fun p => p.1)
      let all_lower := keys.all (fun s => s.toLower = s)
      let all_upper := keys.all (fun s => s.toUpper = s)
      simp [all_lower, all_upper]