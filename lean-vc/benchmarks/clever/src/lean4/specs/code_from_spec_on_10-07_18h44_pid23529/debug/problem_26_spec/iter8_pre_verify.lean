import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def List.count [BEq α] (a : α) : List α → Nat
  | [] => 0
  | (b :: bs) => if a == b then List.count a bs + 1 else List.count a bs

-- LLM HELPER
def List.filter (p : α → Bool) : List α → List α
  | [] => []
  | (a :: as) => if p a then a :: List.filter p as else List.filter p as

-- LLM HELPER
lemma List.mem_filter {α : Type*} (p : α → Bool) (l : List α) (a : α) :
  a ∈ List.filter p l ↔ a ∈ l ∧ p a := by
  induction l with
  | nil => simp [List.filter]
  | cons head tail ih =>
    simp [List.filter]
    split_ifs with h
    · simp [h, ih]
    · simp [h, ih]

-- LLM HELPER
lemma List.mem_of_mem_filter {α : Type*} (p : α → Bool) (l : List α) (a : α) :
  a ∈ List.filter p l → a ∈ l := by
  intro h
  rw [List.mem_filter] at h
  exact h.1

-- LLM HELPER
instance : BEq Int := ⟨fun a b => a == b⟩

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → List.count i numbers = 1) ∧
(∀ i: Int, i ∈ numbers → List.count i numbers = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def filterUnique (numbers: List Int) : List Int :=
  List.filter (fun x => List.count x numbers = 1) numbers

def implementation (numbers: List Int) : List Int := filterUnique numbers

-- LLM HELPER
lemma mem_filterUnique_iff {numbers : List Int} {x : Int} :
  x ∈ filterUnique numbers ↔ x ∈ numbers ∧ List.count x numbers = 1 := by
  unfold filterUnique
  rw [List.mem_filter]
  simp

-- LLM HELPER
lemma filterUnique_subset (numbers : List Int) : ∀ x, x ∈ filterUnique numbers → x ∈ numbers := by
  unfold filterUnique
  intro x hx
  exact List.mem_of_mem_filter _ _ _ hx

-- LLM HELPER
lemma getElem_mem (l : List Int) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  induction' l with head tail ih generalizing i
  · simp at h
  · cases' i with i'
    · simp
    · simp
      apply ih
      simp at h
      exact Nat.lt_of_succ_lt_succ h

-- LLM HELPER
lemma findIndex_exists (numbers : List Int) (x : Int) (h : x ∈ numbers) :
  ∃ i, i < numbers.length ∧ numbers[i]! = x := by
  induction' numbers with head tail ih
  · simp at h
  · simp at h
    cases' h with h h
    · use 0
      simp [h]
    · obtain ⟨i, hi_lt, hi_eq⟩ := ih h
      use i + 1
      simp [hi_eq, hi_lt]

-- LLM HELPER
lemma filter_preserves_order (numbers : List Int) (i j : Nat) :
  i < (filterUnique numbers).length → j < (filterUnique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
  (filterUnique numbers)[i]! = numbers[ip]! ∧
  (filterUnique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  
  unfold filterUnique
  
  have h_i_mem : (List.filter (fun x => List.count x numbers = 1) numbers)[i]! ∈ numbers := by
    have : (List.filter (fun x => List.count x numbers = 1) numbers)[i]! ∈ List.filter (fun x => List.count x numbers = 1) numbers := 
      getElem_mem _ i hi
    exact List.mem_of_mem_filter _ _ _ this
  
  have h_j_mem : (List.filter (fun x => List.count x numbers = 1) numbers)[j]! ∈ numbers := by
    have : (List.filter (fun x => List.count x numbers = 1) numbers)[j]! ∈ List.filter (fun x => List.count x numbers = 1) numbers := 
      getElem_mem _ j hj
    exact List.mem_of_mem_filter _ _ _ this
  
  obtain ⟨ip, hip_lt, hip_eq⟩ := findIndex_exists numbers (List.filter (fun x => List.count x numbers = 1) numbers)[i]! h_i_mem
  obtain ⟨jp, hjp_lt, hjp_eq⟩ := findIndex_exists numbers (List.filter (fun x => List.count x numbers = 1) numbers)[j]! h_j_mem
  
  have h_order : ip < jp := by
    by_contra h_not
    have h_ge : jp ≤ ip := Nat.le_of_not_gt h_not
    
    -- Since filter preserves order, if jp ≤ ip, then j should come before or at i in filtered list
    -- But we have i < j, which is a contradiction
    -- We'll prove this by induction on the structure of filtering
    have h_contra : j ≤ i := by
      -- This follows from the fact that filter preserves relative order
      -- and if the original indices are in reverse order, so are the filtered indices
      induction' numbers with head tail ih generalizing i j ip jp
      · simp at hi
      · simp [List.filter] at hi hj hip_eq hjp_eq
        split_ifs with h_head
        · -- head is included in filter
          cases' ip with ip'
          · -- ip = 0, so head is the i-th element of filtered list
            simp at hip_eq
            rw [← hip_eq] at hjp_eq
            cases' jp with jp'
            · -- jp = 0, contradiction since we assumed jp ≤ ip and ip = 0
              simp at hjp_eq
              rw [hip_eq] at hjp_eq
              have : i = j := by
                -- Both refer to the same element, so i = j
                have h_eq_elem : (List.filter (fun x => List.count x numbers = 1) numbers)[i]! = (List.filter (fun x => List.count x numbers = 1) numbers)[j]! := by
                  rw [hip_eq, hjp_eq]
                simp [List.filter] at h_eq_elem
                split_ifs at h_eq_elem
                · cases' i with i'
                  · cases' j with j'
                    · rfl
                    · simp at h_eq_elem
                      have : head = (List.filter (fun x => List.count x tail = 1) tail)[j']! := h_eq_elem
                      exfalso
                      exact Nat.lt_irrefl _ hij
                  · exfalso
                    exact Nat.lt_irrefl _ hij
                · exfalso
                  exact Nat.lt_irrefl _ hij
              rw [this] at hij
              exact Nat.lt_irrefl _ hij
            · -- jp = jp' + 1, so the j-th element comes from tail
              simp at hjp_eq
              have : j > 0 := by
                cases' j with j'
                · simp at hj
                  split_ifs at hj
                  · simp at hj
                    have : 0 < 1 := by norm_num
                    exact Nat.lt_of_succ_le_succ this
                  · simp at hj
                · exact Nat.zero_lt_succ _
              cases' j with j'
              · exact Nat.lt_irrefl _ this
              · have : j' < (List.filter (fun x => List.count x tail = 1) tail).length := by
                  simp at hj
                  split_ifs at hj
                  · exact Nat.lt_of_succ_lt_succ hj
                  · exact hj
                have : i = 0 := by
                  cases' i with i'
                  · rfl
                  · simp at hi
                    split_ifs at hi
                    · exact Nat.lt_irrefl _ (Nat.lt_of_succ_lt_succ hi)
                    · exact Nat.lt_irrefl _ hi
                rw [this] at hij
                exact Nat.not_lt_zero _ hij
          · -- ip = ip' + 1, so both elements come from tail
            simp at hip_eq
            cases' jp with jp'
            · simp at hjp_eq
              have : False := by
                have : jp < ip := by
                  simp [Nat.zero_lt_succ]
                exact Nat.not_le_of_gt this h_ge
              exact this
            · simp at hjp_eq
              have : ip' < jp' := by
                exact Nat.lt_of_succ_lt_succ (Nat.lt_of_not_ge h_not)
              -- Apply induction hypothesis
              exact Nat.le_refl _
        · -- head is not included in filter
          cases' ip with ip'
          · simp at hip_eq
          · simp at hip_eq
            cases' jp with jp'
            · simp at hjp_eq
            · simp at hjp_eq
              -- Both elements come from tail, apply induction
              exact Nat.le_refl _
    
    exact Nat.not_lt_of_ge h_contra hij
  
  use ip, jp
  exact ⟨h_order, hip_eq, hjp_eq⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  use filterUnique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      rw [mem_filterUnique_iff] at hi
      exact hi.2
    · constructor
      · intro i hi hcount
        rw [mem_filterUnique_iff]
        exact ⟨hi, hcount⟩
      · exact filter_preserves_order numbers