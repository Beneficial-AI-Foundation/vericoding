import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Rat → Rat → Rat → Bool)
(a: Rat) (b: Rat) (c: Rat) :=
let spec (result : Bool) :=
  let nums := [a, b, c];
  result = true ↔ ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ a.den = b.den ∧ a.den = c.den
∃ result,
  implementation a b c = result ∧
  spec result

-- LLM HELPER
def is_integer (r : Rat) : Bool := r.den = 1

-- LLM HELPER
def check_triple_sum (a b c : Rat) : Bool :=
  (a + b = c) ∨ (a + c = b) ∨ (b + c = a)

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool := 
  decide (is_integer a ∧ is_integer b ∧ is_integer c ∧ check_triple_sum a b c)

-- LLM HELPER
lemma triple_list_access (a b c : Rat) : 
  [a, b, c][0]! = a ∧ [a, b, c][1]! = b ∧ [a, b, c][2]! = c := by
  simp [List.getElem!_cons_zero, List.getElem!_cons_succ]

-- LLM HELPER
lemma triple_indices_exist (a b c : Rat) : 
  ((a + b = c) ∨ (a + c = b) ∨ (b + c = a)) ↔ 
  ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ ([a, b, c][i]! + [a, b, c][j]! = [a, b, c][k]!) := by
  constructor
  · intro h
    cases' h with h h
    · -- a + b = c, so indices 0, 1, 2
      use 0, 1, 2
      constructor
      · simp [Set.subset_def]
      constructor
      · norm_num
      constructor  
      · norm_num
      constructor
      · norm_num
      · have := triple_list_access a b c
        simp [this.1, this.2.1, this.2.2]
        exact h
    cases' h with h h
    · -- a + c = b, so indices 0, 2, 1
      use 0, 2, 1
      constructor
      · simp [Set.subset_def]
      constructor
      · norm_num
      constructor
      · norm_num  
      constructor
      · norm_num
      · have := triple_list_access a b c
        simp [this.1, this.2.1, this.2.2]
        exact h
    · -- b + c = a, so indices 1, 2, 0
      use 1, 2, 0
      constructor
      · simp [Set.subset_def]
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · have := triple_list_access a b c
        simp [this.1, this.2.1, this.2.2]
        exact h
  · intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum⟩
    -- Need to consider all possible values of i, j, k
    have h_vals : i ∈ ({0, 1, 2} : Set ℕ) ∧ j ∈ ({0, 1, 2} : Set ℕ) ∧ k ∈ ({0, 1, 2} : Set ℕ) := by
      simp [Set.subset_def] at h_sub
      exact ⟨h_sub i (by simp), h_sub j (by simp), h_sub k (by simp)⟩
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by simp at h_vals; exact h_vals.1
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp at h_vals; exact h_vals.2.1
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by simp at h_vals; exact h_vals.2.2
    
    have access := triple_list_access a b c
    -- Check all possible combinations
    cases' hi with hi hi
    · -- i = 0
      cases' hj with hj hj
      · -- j = 0, but i ≠ j
        exfalso; exact h_ij (hi.trans hj.symm)
      cases' hj with hj hj
      · -- j = 1
        cases' hk with hk hk
        · -- k = 0, but k ≠ i
          exfalso; exact h_ki (hk.trans hi.symm)
        cases' hk with hk hk
        · -- k = 1, but j ≠ k
          exfalso; exact h_jk (hj.trans hk.symm)
        · -- k = 2, so i=0, j=1, k=2
          subst hi hj hk
          simp [access.1, access.2.1, access.2.2] at h_sum
          left; exact h_sum
      · -- j = 2
        cases' hk with hk hk
        · -- k = 0, but k ≠ i
          exfalso; exact h_ki (hk.trans hi.symm)
        cases' hk with hk hk
        · -- k = 1, so i=0, j=2, k=1
          subst hi hj hk
          simp [access.1, access.2.1, access.2.2] at h_sum
          right; left; exact h_sum
        · -- k = 2, but j ≠ k
          exfalso; exact h_jk (hj.trans hk.symm)
    cases' hi with hi hi
    · -- i = 1
      cases' hj with hj hj
      · -- j = 0
        cases' hk with hk hk
        · -- k = 0, but j ≠ k
          exfalso; exact h_jk (hj.trans hk.symm)
        cases' hk with hk hk
        · -- k = 1, but i ≠ k
          exfalso; exact h_ki (hk.trans hi.symm)
        · -- k = 2, so i=1, j=0, k=2
          subst hi hj hk
          simp [access.1, access.2.1, access.2.2] at h_sum
          left; linarith
      cases' hj with hj hj
      · -- j = 1, but i ≠ j
        exfalso; exact h_ij (hi.trans hj.symm)
      · -- j = 2
        cases' hk with hk hk
        · -- k = 0, so i=1, j=2, k=0
          subst hi hj hk
          simp [access.1, access.2.1, access.2.2] at h_sum
          right; right; exact h_sum
        cases' hk with hk hk
        · -- k = 1, but i ≠ k
          exfalso; exact h_ki (hk.trans hi.symm)
        · -- k = 2, but j ≠ k
          exfalso; exact h_jk (hj.trans hk.symm)
    · -- i = 2
      cases' hj with hj hj
      · -- j = 0
        cases' hk with hk hk
        · -- k = 0, but j ≠ k
          exfalso; exact h_jk (hj.trans hk.symm)
        cases' hk with hk hk
        · -- k = 1, so i=2, j=0, k=1
          subst hi hj hk
          simp [access.1, access.2.1, access.2.2] at h_sum
          right; left; linarith
        · -- k = 2, but i ≠ k
          exfalso; exact h_ki (hk.trans hi.symm)
      cases' hj with hj hj
      · -- j = 1
        cases' hk with hk hk
        · -- k = 0, so i=2, j=1, k=0
          subst hi hj hk
          simp [access.1, access.2.1, access.2.2] at h_sum
          right; right; linarith
        cases' hk with hk hk
        · -- k = 1, but j ≠ k
          exfalso; exact h_jk (hj.trans hk.symm)
        · -- k = 2, but i ≠ k
          exfalso; exact h_ki (hk.trans hi.symm)
      · -- j = 2, but i ≠ j
        exfalso; exact h_ij (hi.trans hj.symm)

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  unfold problem_spec implementation is_integer check_triple_sum
  use (a.den = 1 ∧ b.den = 1 ∧ c.den = 1 ∧ ((a + b = c) ∨ (a + c = b) ∨ (b + c = a)))
  constructor
  · simp [Bool.and_eq_true, decide_eq_true_iff]
  · constructor
    · intro h
      rw [triple_indices_exist]
      exact ⟨h.1, h.2.1, h.2.1, h.2.2⟩
    · intro ⟨i, j, k, h_sub, h_ij, h_jk, h_ki, h_sum, h_a, h_b, h_c⟩
      constructor
      · exact h_a
      constructor
      · exact h_b  
      constructor
      · exact h_c
      · rw [← triple_indices_exist]
        use i, j, k
        exact ⟨h_sub, h_ij, h_jk, h_ki, h_sum⟩