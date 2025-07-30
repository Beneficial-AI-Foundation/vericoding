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

-- LLM HELPER
lemma List.length_erase_of_mem {α : Type*} [DecidableEq α] (l : List α) (a : α) (h : a ∈ l) : (l.erase a).length < l.length := by
  have : l.erase a ⊆ l := List.erase_subset _ _
  have : (l.erase a).length ≤ l.length := List.length_le_of_sublist (List.sublist_of_subset this)
  by_cases h_eq : l.erase a = l
  · rw [List.erase_eq_self] at h_eq
    exact absurd h h_eq
  · exact Nat.lt_of_le_of_ne this (Ne.symm (List.ne_of_ne_length (Ne.symm h_eq)))

def implementation (lst: List String) : List String :=
  match findMinEvenString lst with
  | none => []
  | some head => head :: implementation (lst.erase head)
termination_by lst.length
decreasing_by
  simp_wf
  cases' h : findMinEvenString lst with
  | none => simp at *
  | some head =>
    have h_mem : head ∈ lst := by
      unfold findMinEvenString at h
      simp at h
      cases' lst.filter (fun s => Even s.length) with
      | nil => simp at h
      | cons a as => 
        simp at h
        have : head ∈ lst.filter (fun s => Even s.length) := by
          simp [List.mem_filter]
          cases' h with
          | inl h_eq => 
            rw [← h_eq]
            simp [List.mem_filter]
            exact ⟨List.mem_of_mem_filter (List.mem_cons_self a as), by simp [List.mem_filter] at *; exact List.mem_of_mem_filter (List.mem_cons_self a as)⟩
          | inr h_min =>
            simp [List.mem_filter] at h_min
            exact h_min.1
        simp [List.mem_filter] at this
        exact this.1
    exact List.length_erase_of_mem lst head h_mem

-- LLM HELPER
lemma findMinEvenString_none_iff (lst: List String) :
  findMinEvenString lst = none ↔ ∀ str ∈ lst, Odd str.length := by
  constructor
  · intro h str hstr
    unfold findMinEvenString at h
    simp at h
    have : str ∉ lst.filter (fun s => Even s.length) := by
      rw [List.filter_eq_nil] at h
      exact h str hstr
    simp [List.mem_filter] at this
    have : ¬Even str.length := this hstr
    unfold Even Odd at *
    cases' Nat.mod_two_eq_zero_or_one str.length with
    | inl h_even => contradiction
    | inr h_odd => exact h_odd
  · intro h
    unfold findMinEvenString
    simp
    rw [List.filter_eq_nil]
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
  cases' lst.filter (fun s => Even s.length) with
  | nil => simp at h
  | cons a as =>
    simp at h
    constructor
    · -- Even head.length
      have head_in_filtered : head ∈ lst.filter (fun s => Even s.length) := by
        cases' h with
        | inl h_eq => 
          rw [← h_eq]
          exact List.mem_cons_self a as
        | inr h_min =>
          exact h_min.1
      simp [List.mem_filter] at head_in_filtered
      exact head_in_filtered.2
    constructor
    · -- head ∈ lst
      have head_in_filtered : head ∈ lst.filter (fun s => Even s.length) := by
        cases' h with
        | inl h_eq => 
          rw [← h_eq]
          exact List.mem_cons_self a as
        | inr h_min =>
          exact h_min.1
      simp [List.mem_filter] at head_in_filtered
      exact head_in_filtered.1
    · -- ∀ str ∈ lst, ...
      intro str hstr
      by_cases hstr_even : Even str.length
      · right
        right
        have hstr_in_filtered : str ∈ lst.filter (fun s => Even s.length) := by
          simp [List.mem_filter]
          exact ⟨hstr, hstr_even⟩
        cases' h with
        | inl h_eq => 
          rw [← h_eq]
          constructor
          · rfl
          · exact le_refl _
        | inr h_min =>
          exact h_min.2 str hstr_in_filtered
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