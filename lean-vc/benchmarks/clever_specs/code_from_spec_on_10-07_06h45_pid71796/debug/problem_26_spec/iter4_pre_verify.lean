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
    -- This follows from the structure of the filter operation
    -- We can use the fact that i < j and the filter operation preserves order
    induction l generalizing i j ip jp with
    | nil =>
      simp [List.filter] at hi
    | cons head tail ih =>
      simp [List.filter] at hip_eq hjp_eq
      split at hip_eq hjp_eq
      · -- p head = true
        cases' i with i <;> cases' j with j
        · simp at hij
        · -- i = 0, j = j + 1
          simp at hip_eq hjp_eq
          cases' ip with ip
          · simp at hip_eq
            subst hip_eq
            cases' jp with jp
            · simp at hjp_eq
              have : (tail.filter p)[j]! = head := hjp_eq
              have : head ∈ tail.filter p := by
                rw [← this]
                exact List.getElem_mem _ _ _
              have : head ∈ tail := List.mem_of_mem_filter this
              -- This is impossible since head is not in tail
              exact False.elim (List.not_mem_of_cons_cons this)
            · exact Nat.zero_lt_succ _
          · simp at hip_eq
            exact Nat.zero_lt_succ _
        · simp at hij
        · -- i = i + 1, j = j + 1
          simp at hi hj hij hip_eq hjp_eq
          cases' ip with ip <;> cases' jp with jp
          · simp at hip_eq hjp_eq
            have : ip < jp := by
              apply ih i j hi hj (Nat.lt_of_succ_lt_succ hij) 0 0 hip_eq hjp_eq
            exact this
          · simp at hip_eq hjp_eq
            exact Nat.zero_lt_succ _
          · simp at hip_eq hjp_eq
            have : False := by
              have : ip < jp := by
                apply ih i j hi hj (Nat.lt_of_succ_lt_succ hij) ip 0 hip_eq hjp_eq
              exact Nat.not_lt_zero _ this
            exact False.elim this
          · simp at hip_eq hjp_eq
            have : ip < jp := by
              apply ih i j hi hj (Nat.lt_of_succ_lt_succ hij) ip jp hip_eq hjp_eq
            exact Nat.succ_lt_succ this
      · -- p head = false
        have : ip < jp := by
          apply ih i j hi hj hij ip jp hip_eq hjp_eq
        cases' ip with ip <;> cases' jp with jp
        · exact this
        · exact Nat.zero_lt_succ _
        · exact False.elim (Nat.not_lt_zero _ this)
        · exact Nat.succ_lt_succ this
  
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