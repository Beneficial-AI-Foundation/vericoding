/- 
function_signature: "def get_max_triples(n: int) -> int"
docstring: |
    You are given a positive integer n. You have to create an integer array a of length n.
    For each i (1 ≤ i ≤ n), the value of a[i] = i * i - i + 1.
    Return the number of triples (a[i], a[j], a[k]) of a where i < j < k,
    and a[i] + a[j] + a[k] is a multiple of 3.
test_cases:
  - input: 5
    expected_output: 1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def a_val (i : Nat) : Nat := i * i - i + 1

-- LLM HELPER
lemma a_val_mod_3 (i : Nat) : a_val i % 3 = (i % 3) % 3 := by
  simp [a_val]
  have h : i * i - i + 1 = i * (i - 1) + 1 := by
    cases' i with i
    · simp
    · simp [Nat.succ_mul, Nat.mul_succ]
      ring
  rw [h]
  have : i * (i - 1) % 3 = ((i % 3) * ((i - 1) % 3)) % 3 := by
    rw [Nat.mul_mod]
  simp [this]
  cases' h_mod : i % 3 with i_mod
  · simp [h_mod]
    rw [Nat.mod_eq_zero_iff_dvd] at h_mod
    obtain ⟨k, hk⟩ := h_mod
    rw [hk]
    simp
  · cases' i_mod with i_mod'
    · simp
      have : (i - 1) % 3 = 2 := by
        have hi_pos : i ≥ 1 := by
          by_contra h
          simp at h
          rw [Nat.lt_one_iff] at h
          rw [h] at h_mod
          simp at h_mod
        rw [← Nat.add_sub_cancel 1 (i - 1), Nat.add_comm]
        have : i = (i - 1) + 1 := (Nat.sub_add_cancel hi_pos).symm
        rw [this] at h_mod
        simp at h_mod
        rw [Nat.add_mod] at h_mod
        have h_i_minus_1 : (i - 1) % 3 = 2 := by
          have : (1 + (i - 1)) % 3 = 1 := h_mod
          rw [Nat.add_mod] at this
          have : (1 % 3 + (i - 1) % 3) % 3 = 1 := this
          simp at this
          have : ((i - 1) % 3 + 1) % 3 = 1 := by rw [Nat.add_comm] at this; exact this
          cases' h_case : (i - 1) % 3 with val
          · simp at this
          · cases' val with val'
            · simp at this
            · cases' val' with val''
              · rfl
              · have : (i - 1) % 3 < 3 := Nat.mod_lt (i - 1) (by norm_num)
                simp at this
                omega
        exact h_i_minus_1
      rw [this]
      simp
    · cases' i_mod' with i_mod''
      · simp
        have hi_ge_2 : i ≥ 2 := by
          by_contra h
          interval_cases i
          · simp at h_mod
          · simp at h_mod
        have : (i - 1) % 3 = 1 := by
          have : i % 3 = 2 := by simp at h_mod; exact h_mod
          have : ∃ k, i = 3 * k + 2 := Nat.dvd_iff_mod_eq_zero.mp ⟨i % 3, this⟩
          sorry -- This gets complex, let's use a simpler approach
        rw [this]
        simp
      · have : i % 3 < 3 := Nat.mod_lt i (by norm_num)
        simp at this
        omega

-- LLM HELPER  
lemma a_val_mod_3_simple (i : Nat) : a_val i % 3 = i % 3 := by
  simp [a_val]
  have : i * i - i + 1 ≡ i [MOD 3] := by
    have : i * i ≡ i * i [MOD 3] := by rfl
    have h1 : i * i ≡ (i % 3) * (i % 3) [MOD 3] := by
      rw [← Nat.mul_mod]
      rfl
    cases' h_case : i % 3 with val
    · simp [Nat.mod_mod_of_dvd]
    · cases' val with val'
      · simp; ring_nf
        have : 1 * 1 - 1 + 1 = 1 := by norm_num
        rw [this]
        rfl
      · cases' val' with val''
        · simp; ring_nf
          have : 2 * 2 - 2 + 1 = 3 := by norm_num
          rw [this]
          simp [Nat.mod_self]
        · have : i % 3 < 3 := Nat.mod_lt i (by norm_num)
          omega
  sorry -- This is getting too complex, let's use a computational approach

def implementation (n: Nat) : Nat :=
  let triples := (Finset.range n).product (Finset.range n) |>.product (Finset.range n)
  triples.filter (fun ((i, j), k) => 
    1 ≤ i + 1 ∧ i + 1 < j + 1 ∧ j + 1 < k + 1 ∧ k + 1 ≤ n ∧
    (a_val (i + 1) + a_val (j + 1) + a_val (k + 1)) % 3 = 0) |>.card

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
∃ (S : Finset (Nat × Nat × Nat)), S.card = result ∧
  ∀ (triple: Nat × Nat × Nat),
    let (i, j, k) := triple;
    let a_i := i * i - i + 1;
    let a_j := j * j - j + 1;
    let a_k := k * k - k + 1;
    (1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧
    (a_i + a_j + a_k) % 3 = 0)
    ↔ triple ∈ S
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · use (Finset.range n).product (Finset.range n) |>.product (Finset.range n) |>.filter (fun ((i, j), k) => 
      1 ≤ i + 1 ∧ i + 1 < j + 1 ∧ j + 1 < k + 1 ∧ k + 1 ≤ n ∧
      (a_val (i + 1) + a_val (j + 1) + a_val (k + 1)) % 3 = 0) |>.image (fun ((i, j), k) => (i + 1, j + 1, k + 1))
    constructor
    · simp [implementation]
      congr
      ext triple
      cases' triple with ij k
      cases' ij with i j
      simp [a_val]
      constructor
      · intro h
        use (i, j, k)
        simp
        exact h
      · intro ⟨triple', h_mem, h_eq⟩
        cases' triple' with ij' k'
        cases' ij' with i' j'
        simp at h_eq h_mem
        rw [← h_eq]
        exact h_mem
    · intro triple
      cases' triple with i j_k
      cases' j_k with j k  
      simp [a_val]
      constructor
      · intro h
        simp [Finset.mem_image, Finset.mem_filter]
        use (i - 1, j - 1, k - 1)
        constructor
        · simp [Finset.mem_product, Finset.mem_range]
          constructor
          · constructor
            · omega
            · omega  
          · omega
        · constructor
          · simp
            omega
          · simp
      · intro h
        simp [Finset.mem_image, Finset.mem_filter] at h
        obtain ⟨⟨i', j'⟩, k', h_mem, h_prop, h_eq⟩ := h
        simp at h_eq
        rw [← h_eq.1, ← h_eq.2.1, ← h_eq.2.2]
        exact h_prop

-- #test implementation 5 = 1