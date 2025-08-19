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
        use 0
        constructor
        · exact Nat.zero_lt_succ _
        · rfl
      · simp at hi
        obtain ⟨j, hj_bound, hj_eq⟩ := ih i hi
        use j + 1
        constructor
        · exact Nat.succ_lt_succ hj_bound
        · exact hj_eq
    · -- p head = false
      obtain ⟨j, hj_bound, hj_eq⟩ := ih i hi
      use j + 1
      constructor
      · exact Nat.succ_lt_succ hj_bound
      · exact hj_eq

-- LLM HELPER
lemma List.filter_preserves_order {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp, ip < jp ∧ (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro i j hi hj hij
  obtain ⟨ip, hip_bound, hip_eq⟩ := List.getElem_filter_exists l p i hi
  obtain ⟨jp, hjp_bound, hjp_eq⟩ := List.getElem_filter_exists l p j hj
  
  -- We need to show that ip < jp
  have ip_lt_jp : ip < jp := by
    -- We prove this by induction on the list structure
    -- The key insight is that filter maintains relative order
    
    -- We can prove this by strong induction on the original list
    -- showing that filter preserves the relative positions
    have h : ∀ (xs : List α) (pred : α → Bool) (a b : Nat) (ia ib : Nat),
      a < (xs.filter pred).length → 
      b < (xs.filter pred).length → 
      a < b →
      ia < xs.length →
      ib < xs.length →
      (xs.filter pred)[a]! = xs[ia]! →
      (xs.filter pred)[b]! = xs[ib]! →
      ia < ib := by
      intro xs pred a b ia ib ha hb hab hia hib heqa heqb
      -- Prove by induction on xs
      induction xs generalizing a b ia ib with
      | nil => simp [List.filter] at ha
      | cons head tail ih =>
        simp [List.filter] at ha hb heqa heqb
        split at ha hb heqa heqb
        · -- pred head = true case
          cases' a with a' <;> cases' b with b'
          · simp at hab
          · -- a = 0, b = b'+1
            simp at heqa heqb
            cases' ia with ia' <;> cases' ib with ib'
            · simp at heqa heqb
              simp at hib
              exact Nat.zero_lt_succ _
            · simp at heqa
              simp at hib
              exact Nat.zero_lt_succ _
            · simp at heqa
              contradiction
            · simp at heqa
              simp at hib
              exact Nat.zero_lt_succ _
          · simp at hab
          · -- a = a'+1, b = b'+1
            simp at ha hb hab heqa heqb
            cases' ia with ia' <;> cases' ib with ib'
            · simp at heqa
              simp at hia
              have : a' < (tail.filter pred).length := ha
              have : (tail.filter pred)[a']! = head := by simp at heqa; exact heqa
              have : ∃ k, k < tail.length ∧ (tail.filter pred)[a']! = tail[k]! := 
                List.getElem_filter_exists tail pred a' this
              obtain ⟨k, _, hk_eq⟩ := this
              simp at hk_eq
              rw [hk_eq] at heqa
              simp at heqa
            · simp at heqa
              simp at hia
              exact Nat.zero_lt_succ _
            · simp at heqb
              simp at hib
              have : b' < (tail.filter pred).length := hb
              have : (tail.filter pred)[b']! = head := by simp at heqb; exact heqb
              have : ∃ k, k < tail.length ∧ (tail.filter pred)[b']! = tail[k]! := 
                List.getElem_filter_exists tail pred b' this
              obtain ⟨k, _, hk_eq⟩ := this
              simp at hk_eq
              rw [hk_eq] at heqb
              simp at heqb
            · simp at heqa heqb
              simp at hia hib
              have : a' < b' := Nat.lt_of_succ_lt_succ hab
              exact Nat.succ_lt_succ (ih a' b' ia' ib' ha hb this hia hib heqa heqb)
        · -- pred head = false case
          cases' ia with ia' <;> cases' ib with ib'
          · simp at hia
          · simp at hia
            exact Nat.zero_lt_succ _
          · simp at hib
          · simp at hia hib
            exact Nat.succ_lt_succ (ih a b ia' ib' ha hb hab hia hib heqa heqb)
    
    exact h l p i j ip jp hi hj hij hip_bound hjp_bound hip_eq hjp_eq
  
  exact ⟨ip, jp, ip_lt_jp, hip_eq, hjp_eq⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
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
    exact List.filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij