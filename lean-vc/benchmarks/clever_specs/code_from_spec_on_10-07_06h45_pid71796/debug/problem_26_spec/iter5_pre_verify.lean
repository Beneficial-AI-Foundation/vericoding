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
lemma List.getElem_filter_exists {α : Type*} (l : List α) (p : α → Bool) (i : Nat) 
  (hi : i < (l.filter p).length) : ∃ j, j < l.length ∧ (l.filter p)[i]! = l[j]! := by
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
lemma List.filter_preserves_order {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp, ip < jp ∧ (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro i j hi hj hij
  obtain ⟨ip, hip_bound, hip_eq⟩ := List.getElem_filter_exists l p i hi
  obtain ⟨jp, hjp_bound, hjp_eq⟩ := List.getElem_filter_exists l p j hj
  
  -- Show that ip < jp by using the fact that filter maintains relative order
  have ip_lt_jp : ip < jp := by
    -- We prove this by contradiction
    by_contra h
    push_neg at h
    -- If jp ≤ ip, then the filter would have j appearing before or at the same position as i
    -- But we know i < j in the filtered list
    -- This is a simplified approach - in practice we'd need a more detailed proof
    -- about how filter preserves order
    have : j ≤ i := by
      -- This follows from the structure of filter operation
      -- If jp ≤ ip, then j must appear before or at position i in the filtered list
      induction l generalizing i j ip jp with
      | nil => simp [List.filter] at hi
      | cons head tail ih =>
        simp [List.filter] at *
        split
        · -- p head = true
          cases' i with i <;> cases' j with j
          · simp at hij
          · simp at hip_eq hjp_eq
            cases' ip with ip
            · simp at hip_eq
              subst hip_eq
              cases' jp with jp
              · simp at hjp_eq
                subst hjp_eq
                simp at h
              · simp at hjp_eq
                have : 0 < jp + 1 := Nat.zero_lt_succ _
                exact False.elim (h this)
            · simp at hip_eq
              cases' jp with jp
              · simp at hjp_eq
                have : jp + 1 < ip + 1 := by
                  apply ih j 0 (by simp at hj; exact hj) (by simp at hip_eq; exact hip_eq) hjp_eq
                exact Nat.succ_le_succ (Nat.le_of_lt_succ this)
              · simp at hip_eq hjp_eq
                have : jp + 1 ≤ ip + 1 := by
                  apply Nat.succ_le_succ
                  apply Nat.le_of_not_gt
                  intro hjp_ip
                  have : j < i := by
                    apply ih i j (by simp at hi; exact hi) (by simp at hj; exact hj) (Nat.lt_of_succ_lt_succ hij) ip jp hip_eq hjp_eq
                  exact Nat.not_lt.mpr (Nat.le_of_lt_succ this) hij
                exact this
          · simp at hij
          · simp at hi hj hij hip_eq hjp_eq
            cases' ip with ip <;> cases' jp with jp
            · simp at hip_eq hjp_eq
              have : j ≤ i := by
                apply ih i j hi hj (Nat.lt_of_succ_lt_succ hij) 0 0 hip_eq hjp_eq
              exact Nat.succ_le_succ this
            · simp at hip_eq hjp_eq
              have : j ≤ i := by
                apply ih i j hi hj (Nat.lt_of_succ_lt_succ hij) 0 jp hip_eq hjp_eq
              exact Nat.succ_le_succ this
            · simp at hip_eq hjp_eq
              have : j ≤ i := by
                apply ih i j hi hj (Nat.lt_of_succ_lt_succ hij) ip 0 hip_eq hjp_eq
              exact Nat.succ_le_succ this
            · simp at hip_eq hjp_eq
              have : j ≤ i := by
                apply ih i j hi hj (Nat.lt_of_succ_lt_succ hij) ip jp hip_eq hjp_eq
              exact Nat.succ_le_succ this
        · -- p head = false
          have : j ≤ i := by
            apply ih i j hi hj hij ip jp hip_eq hjp_eq
          exact this
    exact Nat.not_lt.mpr this hij
  
  exact ⟨ip, jp, ip_lt_jp, hip_eq, hjp_eq⟩

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
    have := List.filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij
    obtain ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩ := this
    exact ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩