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
lemma findIndex_lt (numbers : List Int) (x : Int) (h : x ∈ numbers) :
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
lemma filter_order_preserved (p : Int → Bool) (l : List Int) :
  ∀ i j, i < j → 
  ∀ vi vj, (List.filter p l)[i]? = some vi → (List.filter p l)[j]? = some vj →
  ∃ ip jp, ip < jp ∧ l[ip]? = some vi ∧ l[jp]? = some vj := by
  intro i j hij vi vj hvi hvj
  induction' l with head tail ih generalizing i j
  · simp [List.filter] at hvi
  · simp [List.filter] at hvi hvj
    split_ifs with h
    · cases' i with i'
      · simp at hvi
        rw [← hvi] at hvj
        cases' j with j'
        · simp at hvj
          rw [← hvj] at hvi
          have : head = vi := by simp [hvi]
          rw [this] at hvj
          exact Nat.lt_irrefl _ hij
        · simp at hvj
          have : ∃ jp, jp < tail.length ∧ tail[jp]? = some vj := by
            cases' hvj with hvj
            · use 0
              simp [hvj]
            · obtain ⟨jp, hjp_lt, hjp_eq⟩ := findIndex_lt tail vj hvj
              use jp
              simp [hjp_eq, hjp_lt]
          obtain ⟨jp, hjp_lt, hjp_eq⟩ := this
          use 0, jp + 1
          simp [hvi, hjp_eq, hjp_lt]
      · simp at hvi
        cases' j with j'
        · simp at hij
        · simp at hvj
          have : i' < j' := Nat.lt_of_succ_lt_succ hij
          obtain ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩ := ih i' j' this vi vj hvi hvj
          use ip + 1, jp + 1
          simp [hip_jp, hip_eq, hjp_eq]
    · cases' i with i'
      · simp at hvi
        obtain ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩ := ih 0 j hij vi vj hvi hvj
        use ip + 1, jp + 1
        simp [hip_jp, hip_eq, hjp_eq]
      · simp at hvi
        cases' j with j'
        · simp at hij
        · simp at hvj
          have : i' < j' := Nat.lt_of_succ_lt_succ hij
          obtain ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩ := ih i' j' this vi vj hvi hvj
          use ip + 1, jp + 1
          simp [hip_jp, hip_eq, hjp_eq]

-- LLM HELPER
lemma filter_preserves_order (numbers : List Int) (i j : Nat) :
  i < (filterUnique numbers).length → j < (filterUnique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
  (filterUnique numbers)[i]! = numbers[ip]! ∧
  (filterUnique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  
  unfold filterUnique
  
  have hvi : (List.filter (fun x => List.count x numbers = 1) numbers)[i]? = some ((List.filter (fun x => List.count x numbers = 1) numbers)[i]!) := by
    simp [List.getElem?_eq_getElem, hi]
  
  have hvj : (List.filter (fun x => List.count x numbers = 1) numbers)[j]? = some ((List.filter (fun x => List.count x numbers = 1) numbers)[j]!) := by
    simp [List.getElem?_eq_getElem, hj]
  
  obtain ⟨ip, jp, hip_jp, hip_eq, hjp_eq⟩ := filter_order_preserved (fun x => List.count x numbers = 1) numbers i j hij _ _ hvi hvj
  
  use ip, jp
  simp at hip_eq hjp_eq
  exact ⟨hip_jp, hip_eq, hjp_eq⟩

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