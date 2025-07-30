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
def Even (n : Nat) : Prop := n % 2 = 0

-- LLM HELPER
def Odd (n : Nat) : Prop := n % 2 = 1

-- LLM HELPER
instance decidableEven (n : Nat) : Decidable (Even n) := by
  unfold Even
  infer_instance

-- LLM HELPER
instance decidableOdd (n : Nat) : Decidable (Odd n) := by
  unfold Odd
  infer_instance

-- LLM HELPER
def findMinEvenString (lst: List String) : Option String :=
  let evenStrings := lst.filter (fun s => Even s.length)
  match evenStrings with
  | [] => none
  | head :: _ => some (evenStrings.foldl (fun acc s => if s ≤ acc then s else acc) head)

def implementation (lst: List String) : List String :=
  match findMinEvenString lst with
  | none => []
  | some head => head :: implementation (lst.erase head)
termination_by lst.length
decreasing_by
  simp_wf
  cases' findMinEvenString lst with
  | none => simp
  | some head =>
    have h : head ∈ lst := by
      unfold findMinEvenString at *
      simp at *
      have : head ∈ lst.filter (fun s => Even s.length) := by
        by_cases h : lst.filter (fun s => Even s.length) = []
        · simp [h] at *
        · simp [List.ne_nil_iff_exists_mem] at h
          obtain ⟨x, hx⟩ := h
          simp [List.mem_filter] at hx
          simp [List.mem_filter]
          exact ⟨hx.1, hx.2⟩
      simp [List.mem_filter] at this
      exact this.1
    exact List.length_erase_of_mem h

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
    have : ¬Even str.length := this hstr
    unfold Even Odd at *
    cases' Nat.mod_two_eq_zero_or_one str.length with
    | inl h_even => contradiction
    | inr h_odd => exact h_odd
  · intro h
    unfold findMinEvenString
    simp
    ext
    simp [List.mem_filter]
    intro str hstr
    have : Odd str.length := h str hstr
    unfold Even Odd at *
    cases' Nat.mod_two_eq_zero_or_one str.length with
    | inl h_even => rw [h_even] at this; simp at this
    | inr h_odd => rw [h_odd]; simp

-- LLM HELPER
lemma findMinEvenString_some_properties (lst: List String) (head: String) :
  findMinEvenString lst = some head →
  Even head.length ∧ head ∈ lst ∧
  ∀ str ∈ lst, Odd str.length ∨ str.length > head.length ∨ str.length = head.length ∧ str ≥ head := by
  intro h
  unfold findMinEvenString at h
  simp at h
  obtain ⟨heven_nonempty, hmin⟩ := h
  constructor
  · -- Even head.length
    have head_in_filtered : head ∈ lst.filter (fun s => Even s.length) := by
      simp [List.mem_filter] at hmin
      exact hmin.1
    simp [List.mem_filter] at head_in_filtered
    exact head_in_filtered.2
  constructor
  · -- head ∈ lst
    have head_in_filtered : head ∈ lst.filter (fun s => Even s.length) := by
      simp [List.mem_filter] at hmin
      exact hmin.1
    simp [List.mem_filter] at head_in_filtered
    exact head_in_filtered.1
  · -- ∀ str ∈ lst, ...
    intro str hstr
    by_cases hstr_even : Even str.length
    · right
      right
      simp [List.mem_filter] at hmin
      have hstr_in_filtered : str ∈ lst.filter (fun s => Even s.length) := by
        simp [List.mem_filter]
        exact ⟨hstr, hstr_even⟩
      exact hmin.2 str hstr_in_filtered
    · left
      unfold Even Odd at *
      cases' Nat.mod_two_eq_zero_or_one str.length with
      | inl h_even => contradiction
      | inr h_odd => exact h_odd

-- LLM HELPER
lemma implementation_spec (lst: List String) : 
  let result := implementation lst
  match result with
  | [] => ∀ str ∈ lst, Odd str.length
  | head::tail =>
    Even head.length ∧
    (∀ str ∈ lst,
      Odd str.length ∨
      str.length > head.length ∨
      str.length = head.length ∧ str ≥ head)
    ∧ implementation (lst.erase head) = tail := by
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
      · rfl

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · exact implementation_spec lst