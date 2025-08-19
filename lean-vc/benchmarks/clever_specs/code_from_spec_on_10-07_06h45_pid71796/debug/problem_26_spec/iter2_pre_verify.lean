def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def filterUnique (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def implementation (numbers: List Int) : List Int := 
  filterUnique numbers

-- LLM HELPER
lemma filterUnique_correct (numbers: List Int) :
  ∀ x, x ∈ filterUnique numbers ↔ (x ∈ numbers ∧ numbers.count x = 1) := by
  intro x
  simp [filterUnique, List.mem_filter]

-- LLM HELPER
lemma List.filter_preserves_order_indices {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp, ip < l.length ∧ jp < l.length ∧ ip < jp ∧ 
           (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro i j hi hj hij
  -- The key insight: filter preserves relative order from the original list
  have h1 : ∃ ip, ip < l.length ∧ (l.filter p)[i]! = l[ip]! := by
    apply List.getElem_filter_exists
    exact hi
  have h2 : ∃ jp, jp < l.length ∧ (l.filter p)[j]! = l[jp]! := by
    apply List.getElem_filter_exists
    exact hj
  obtain ⟨ip, hip_bound, hip_eq⟩ := h1
  obtain ⟨jp, hjp_bound, hjp_eq⟩ := h2
  
  -- Since filter preserves order, ip < jp
  have ip_lt_jp : ip < jp := by
    apply List.filter_indices_ordered
    · exact hi
    · exact hj
    · exact hij
    · exact hip_eq
    · exact hjp_eq
  
  exact ⟨ip, jp, hip_bound, hjp_bound, ip_lt_jp, hip_eq, hjp_eq⟩

-- LLM HELPER
lemma List.getElem_filter_exists {α : Type*} (l : List α) (p : α → Bool) (i : Nat) :
  i < (l.filter p).length → ∃ j, j < l.length ∧ (l.filter p)[i]! = l[j]! := by
  intro hi
  induction l generalizing i with
  | nil => 
    simp [List.filter] at hi
  | cons head tail ih =>
    simp [List.filter] at hi ⊢
    split at hi
    · -- p head = true
      cases' i with i
      · simp
        exact ⟨0, Nat.zero_lt_succ _, rfl⟩
      · simp at hi
        obtain ⟨j, hj_bound, hj_eq⟩ := ih i hi
        exact ⟨j + 1, Nat.succ_lt_succ hj_bound, hj_eq⟩
    · -- p head = false
      obtain ⟨j, hj_bound, hj_eq⟩ := ih i hi
      exact ⟨j + 1, Nat.succ_lt_succ hj_bound, hj_eq⟩

-- LLM HELPER
lemma List.filter_indices_ordered {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j ip jp, i < (l.filter p).length → j < (l.filter p).length → i < j →
  (l.filter p)[i]! = l[ip]! → (l.filter p)[j]! = l[jp]! → ip < jp := by
  intro i j ip jp hi hj hij hip_eq hjp_eq
  -- This follows from the fact that filter maintains the relative order
  induction l generalizing i j ip jp with
  | nil => 
    simp [List.filter] at hi
  | cons head tail ih =>
    simp [List.filter] at hi hj hip_eq hjp_eq
    split at hi hj hip_eq hjp_eq
    · -- p head = true
      cases' i with i <;> cases' j with j
      · simp at hij
      · -- i = 0, j = j + 1
        simp at hip_eq hjp_eq
        cases' ip with ip
        · simp at hip_eq
          rw [hip_eq] at hjp_eq
          cases' jp with jp
          · simp at hjp_eq
            have : (tail.filter p)[j]! = head := hjp_eq
            have : (tail.filter p)[j]! ∈ tail := List.getElem_mem _ _ _
            rw [this] at this
            have : head ∈ tail := this
            have : ¬(head ∈ tail) := List.not_mem_of_cons_cons
            contradiction
          · exact Nat.zero_lt_succ _
        · simp at hip_eq
          exact Nat.zero_lt_succ _
      · simp at hij
      · -- i = i + 1, j = j + 1
        simp at hi hj hij hip_eq hjp_eq
        cases' ip with ip <;> cases' jp with jp
        · simp at hip_eq hjp_eq
          have := ih i j 0 0 hi hj (Nat.lt_of_succ_lt_succ hij) hip_eq hjp_eq
          exact this
        · simp at hip_eq hjp_eq
          exact Nat.zero_lt_succ _
        · simp at hip_eq hjp_eq
          exact Nat.zero_lt_succ _
        · simp at hip_eq hjp_eq
          have := ih i j ip jp hi hj (Nat.lt_of_succ_lt_succ hij) hip_eq hjp_eq
          exact Nat.succ_lt_succ this
    · -- p head = false
      cases' ip with ip <;> cases' jp with jp
      · simp at hip_eq hjp_eq
        have := ih i j 0 0 hi hj hij hip_eq hjp_eq
        exact this
      · simp at hip_eq hjp_eq
        exact Nat.zero_lt_succ _
      · simp at hip_eq hjp_eq
        exact Nat.zero_lt_succ _
      · simp at hip_eq hjp_eq
        have := ih i j ip jp hi hj hij hip_eq hjp_eq
        exact Nat.succ_lt_succ this

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filterUnique numbers
  constructor
  · rfl
  constructor
  · -- First condition: ∀ i: Int, i ∈ result → numbers.count i = 1
    intro i hi
    rw [filterUnique_correct] at hi
    exact hi.2
  constructor
  · -- Second condition: ∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result
    intro i hi hcount
    rw [filterUnique_correct]
    exact ⟨hi, hcount⟩
  · -- Third condition: order preservation
    intro i j hi hj hij
    have := List.filter_preserves_order_indices numbers (fun x => numbers.count x = 1) i j hi hj hij
    obtain ⟨ip, jp, _, _, hip_jp, hip_eq, hjp_eq⟩ := this
    exact ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩