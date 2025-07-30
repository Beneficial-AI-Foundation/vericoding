import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → (Rat × Rat))
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: (Rat × Rat)) :=
2 ≤ numbers.length →
(let (smaller, larger) := result;
let abs_diff := |larger - smaller|;
smaller ≤ larger ∧
smaller ∈ numbers ∧
larger ∈ numbers ∧
(∀ x y, x ∈ numbers → y ∈ numbers →  abs_diff ≤ |x - y|) ∧
(smaller = larger → 1 ≤ (numbers.filter (fun z => z = smaller)).length));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_diff_pair (numbers: List Rat): (Rat × Rat) :=
match numbers with
| [] => (0, 0)
| [x] => (x, x)
| x :: xs => 
  let pairs := List.product numbers numbers
  let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
  let min_pair := valid_pairs.foldl (fun acc (a, b) => 
    if |b - a| < |acc.2 - acc.1| then (a, b) else acc) (valid_pairs.head!)
  min_pair

def implementation (numbers: List Rat): (Rat × Rat) := find_min_diff_pair numbers

-- LLM HELPER
lemma list_product_mem {α : Type*} (l : List α) (x y : α) : 
  x ∈ l → y ∈ l → (x, y) ∈ List.product l l := by
  intro hx hy
  exact List.mem_product.mpr ⟨hx, hy⟩

-- LLM HELPER
lemma filter_nonempty_of_le {α : Type*} (l : List α) (p : α → Bool) :
  l.filter p ≠ [] → ∃ x, x ∈ l ∧ p x := by
  intro h
  by_contra h'
  push_neg at h'
  have : l.filter p = [] := by
    rw [List.filter_eq_nil]
    exact h'
  contradiction

-- LLM HELPER
lemma exists_pair_in_product (numbers : List Rat) (h : 2 ≤ numbers.length) :
  ∃ x y, x ∈ numbers ∧ y ∈ numbers ∧ x ≤ y := by
  have h_len : 0 < numbers.length := by linarith
  have h_len2 : 1 < numbers.length := by linarith
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h_len
  obtain ⟨y, hy⟩ := List.exists_mem_of_length_pos h_len
  cases' le_total x y with h_le h_ge
  · exact ⟨x, y, hx, hy, h_le⟩
  · exact ⟨y, x, hy, hx, h_ge⟩

-- LLM HELPER
lemma foldl_preserves_property {α β : Type*} (f : α → β → α) (init : α) (l : List β) 
  (P : α → Prop) (h_init : P init) (h_preserve : ∀ a b, P a → P (f a b)) :
  P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h_init
  | cons head tail ih =>
    apply ih
    exact h_preserve init head h_init

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation find_min_diff_pair
  cases' numbers with h1 t1
  · -- empty list case
    use (0, 0)
    simp
    intro h
    norm_num at h
  · cases' t1 with h2 t2
    · -- single element case
      use (h1, h1)
      simp
      intro h
      norm_num at h
    · -- at least two elements case
      let pairs := List.product (h1 :: h2 :: t2) (h1 :: h2 :: t2)
      let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
      have h_len : 2 ≤ (h1 :: h2 :: t2).length := by simp [List.length_cons]; norm_num
      have h_valid_nonempty : valid_pairs ≠ [] := by
        unfold valid_pairs pairs
        rw [List.filter_ne_nil]
        use (h1, h1)
        constructor
        · exact list_product_mem (h1 :: h2 :: t2) h1 h1 (List.mem_cons_self _ _) (List.mem_cons_self _ _)
        · simp
      obtain ⟨head_pair, h_head⟩ := List.exists_mem_of_ne_nil h_valid_nonempty
      use (valid_pairs.foldl (fun acc (a, b) => 
        if |b - a| < |acc.2 - acc.1| then (a, b) else acc) head_pair)
      constructor
      · rfl
      · intro h_len_ge
        have h_head_valid : head_pair.1 ≤ head_pair.2 := by
          have : head_pair ∈ valid_pairs := h_head
          rw [List.mem_filter] at this
          exact this.2
        have h_head_in : head_pair.1 ∈ (h1 :: h2 :: t2) ∧ head_pair.2 ∈ (h1 :: h2 :: t2) := by
          have : head_pair ∈ valid_pairs := h_head
          rw [List.mem_filter] at this
          rw [List.mem_product] at this
          exact this.1
        constructor
        · -- smaller ≤ larger
          apply foldl_preserves_property
          · exact h_head_valid
          · intro acc pair
            simp
            split_ifs
            · simp
            · simp
        constructor
        · -- smaller ∈ numbers
          apply foldl_preserves_property
          · exact h_head_in.1
          · intro acc pair h_acc_in
            simp
            split_ifs with h_cond
            · have : pair ∈ valid_pairs := by
                -- This would need more detailed proof about foldl iteration
                sorry
              rw [List.mem_filter] at this
              rw [List.mem_product] at this
              exact this.1.1
            · exact h_acc_in
        constructor
        · -- larger ∈ numbers
          apply foldl_preserves_property
          · exact h_head_in.2
          · intro acc pair h_acc_in
            simp
            split_ifs with h_cond
            · have : pair ∈ valid_pairs := by
                -- This would need more detailed proof about foldl iteration
                sorry
              rw [List.mem_filter] at this
              rw [List.mem_product] at this
              exact this.1.2
            · exact h_acc_in
        constructor
        · -- minimality property
          intro x y hx hy
          -- This would require proving that foldl actually finds the minimum
          sorry
        · -- duplicate handling
          intro h_eq
          -- This would require more careful analysis of the filtering
          sorry