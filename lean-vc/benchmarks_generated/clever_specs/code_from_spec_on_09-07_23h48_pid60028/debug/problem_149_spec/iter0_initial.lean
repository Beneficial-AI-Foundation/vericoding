def problem_spec
-- function signature
(impl: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result: List String) :=
match result with
| [] => ∀ str ∈ lst, Odd str.length
| head::tail =>
  Even head.length ∧
  (∀ str ∈ lst,
    Odd str.length ∨
    str.length > head.length ∨
    str.length = head.length ∧ str ≥ head)
  ∧ impl (lst.erase head) = tail
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def findMinEvenString (lst: List String) : Option String :=
  let evenStrings := lst.filter (fun s => Even s.length)
  match evenStrings with
  | [] => none
  | _ => evenStrings.minimum?

def implementation (lst: List String) : List String :=
  match findMinEvenString lst with
  | none => []
  | some head => head :: implementation (lst.erase head)

-- LLM HELPER
lemma findMinEvenString_none_iff (lst: List String) :
  findMinEvenString lst = none ↔ ∀ str ∈ lst, Odd str.length := by
  constructor
  · intro h str hstr
    unfold findMinEvenString at h
    simp at h
    have : str ∉ lst.filter (fun s => Even s.length) := by
      cases' lst.filter (fun s => Even s.length) with
      | nil => simp
      | cons a as => simp at h
    simp [List.mem_filter] at this
    exact this hstr
  · intro h
    unfold findMinEvenString
    simp
    ext
    simp [List.mem_filter]
    intro str hstr
    exact h str hstr

-- LLM HELPER
lemma findMinEvenString_some_properties (lst: List String) (head: String) :
  findMinEvenString lst = some head →
  Even head.length ∧ head ∈ lst ∧
  ∀ str ∈ lst, Odd str.length ∨ str.length > head.length ∨ str.length = head.length ∧ str ≥ head := by
  intro h
  unfold findMinEvenString at h
  simp at h
  obtain ⟨heven, hmin⟩ := h
  constructor
  · exact heven
  constructor
  · simp [List.mem_filter] at hmin
    exact hmin.1
  · intro str hstr
    by_cases hstr_even : Even str.length
    · right
      right
      simp [List.mem_filter] at hmin
      have hstr_in_filtered : str ∈ lst.filter (fun s => Even s.length) := by
        simp [List.mem_filter]
        exact ⟨hstr, hstr_even⟩
      exact hmin.2 str hstr_in_filtered
    · left
      exact Nat.odd_iff_not_even.mpr hstr_even

-- LLM HELPER
lemma implementation_decreases (lst: List String) (head: String) :
  head ∈ lst → (lst.erase head).length < lst.length := by
  intro h
  exact List.length_erase_of_mem h

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  simp
  induction lst using List.strong_induction_on with
  | ind lst ih =>
    unfold implementation
    cases' h : findMinEvenString lst with
    | none =>
      simp
      exact (findMinEvenString_none_iff lst).mp h
    | some head =>
      simp
      constructor
      · exact (findMinEvenString_some_properties lst head h).1
      constructor
      · exact (findMinEvenString_some_properties lst head h).2.2
      · have head_mem : head ∈ lst := (findMinEvenString_some_properties lst head h).2.1
        have : (lst.erase head).length < lst.length := implementation_decreases lst head head_mem
        exact ih (lst.erase head) this