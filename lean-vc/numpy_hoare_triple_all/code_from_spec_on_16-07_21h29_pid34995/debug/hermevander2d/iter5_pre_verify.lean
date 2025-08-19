import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermiteE : Nat → Float → Float
  | 0, _ => 1.0
  | 1, t => t
  | n + 2, t => t * hermiteE (n + 1) t - Float.ofNat (n + 1) * hermiteE n t

-- LLM HELPER
def computeEntry (x_val y_val : Float) (i j : Nat) : Float :=
  hermiteE i x_val * hermiteE j y_val

-- LLM HELPER
def buildRow (x_val y_val : Float) (x_deg y_deg : Nat) : Vector Float ((x_deg + 1) * (y_deg + 1)) :=
  Vector.ofFn (fun k => 
    let i := k / (y_deg + 1)
    let j := k % (y_deg + 1)
    computeEntry x_val y_val i j)

def hermevander2d {n : Nat} (x y : Vector Float n) (x_deg y_deg : Nat) : 
    Id (Vector (Vector Float ((x_deg + 1) * (y_deg + 1))) n) :=
  return (Vector.ofFn (fun k => buildRow (x.get k) (y.get k) x_deg y_deg))

-- LLM HELPER
lemma hermiteE_base_0 (t : Float) : hermiteE 0 t = 1 := by
  simp [hermiteE]

-- LLM HELPER
lemma hermiteE_base_1 (t : Float) : hermiteE 1 t = t := by
  simp [hermiteE]

-- LLM HELPER
lemma hermiteE_recurrence (k : Nat) (t : Float) : 
    hermiteE (k + 2) t = t * hermiteE (k + 1) t - Float.ofNat (k + 1) * hermiteE k t := by
  simp [hermiteE]

-- LLM HELPER
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) : 
    (Vector.ofFn f).get i = f i := by
  simp [Vector.ofFn, Vector.get]

-- LLM HELPER
lemma buildRow_size (x_val y_val : Float) (x_deg y_deg : Nat) : 
    (buildRow x_val y_val x_deg y_deg).size = (x_deg + 1) * (y_deg + 1) := by
  simp [buildRow, Vector.size_ofFn]

-- LLM HELPER
lemma buildRow_get (x_val y_val : Float) (x_deg y_deg : Nat) (idx : Fin ((x_deg + 1) * (y_deg + 1))) :
    (buildRow x_val y_val x_deg y_deg).get idx = 
    computeEntry x_val y_val (idx.val / (y_deg + 1)) (idx.val % (y_deg + 1)) := by
  simp [buildRow, vector_get_ofFn, computeEntry]

-- LLM HELPER
lemma hermevander2d_size {n : Nat} (x y : Vector Float n) (x_deg y_deg : Nat) :
    (hermevander2d x y x_deg y_deg).size = n := by
  simp [hermevander2d, Vector.size_ofFn]

-- LLM HELPER
lemma hermevander2d_get {n : Nat} (x y : Vector Float n) (x_deg y_deg : Nat) (i : Fin n) :
    (hermevander2d x y x_deg y_deg).get i = buildRow (x.get i) (y.get i) x_deg y_deg := by
  simp [hermevander2d, vector_get_ofFn]

-- LLM HELPER
lemma div_mod_unique (a b : Nat) (hb : b > 0) : 
    ∃ q r : Nat, a = b * q + r ∧ r < b ∧ q = a / b ∧ r = a % b := by
  use a / b, a % b
  constructor
  · rw [Nat.div_add_mod]
  constructor
  · exact Nat.mod_lt a hb
  constructor <;> simp

theorem hermevander2d_spec {n : Nat} (x y : Vector Float n) (x_deg y_deg : Nat) :
    ⦃⌜True⌝⦄
    hermevander2d x y x_deg y_deg
    ⦃⇓result => ⌜-- Matrix dimensions are correct
                 (∀ point_idx : Fin n, 
                   -- Each row has the correct number of basis functions
                   (result.get point_idx).size = (x_deg + 1) * (y_deg + 1)) ∧
                 -- Matrix entries follow the HermiteE basis structure
                 (∃ hermite_basis : Nat → Float → Float,
                   -- Base cases for HermiteE polynomials
                   (∀ t : Float, hermite_basis 0 t = 1) ∧
                   (∀ t : Float, hermite_basis 1 t = t) ∧
                   -- Recurrence relation: He_{k+1}(x) = x * He_k(x) - k * He_{k-1}(x)
                   (∀ k : Nat, k ≥ 1 → k < max x_deg y_deg → ∀ t : Float, 
                     hermite_basis (k + 1) t = t * hermite_basis k t - Float.ofNat k * hermite_basis (k - 1) t) ∧
                   -- Matrix entries computed correctly using basis functions
                   (∀ point_idx : Fin n, ∀ basis_idx : Fin ((x_deg + 1) * (y_deg + 1)),
                     -- Extract degree indices from basis index
                     ∃ i j : Nat, i ≤ x_deg ∧ j ≤ y_deg ∧ 
                     basis_idx.val = (y_deg + 1) * i + j ∧
                     -- Matrix entry is the product of HermiteE basis functions
                     (result.get point_idx).get basis_idx = 
                       hermite_basis i (x.get point_idx) * hermite_basis j (y.get point_idx))) ∧
                 -- Polynomial evaluation equivalence property exists
                 (∀ coeff_matrix : Vector (Vector Float (y_deg + 1)) (x_deg + 1),
                   ∃ flattened_coeff : Vector Float ((x_deg + 1) * (y_deg + 1)),
                   -- Coefficient flattening follows row-major order
                   (∀ i : Fin (x_deg + 1), ∀ j : Fin (y_deg + 1),
                     flattened_coeff.get ⟨(y_deg + 1) * i.val + j.val, by
                       have h1 : i.val < x_deg + 1 := i.isLt
                       have h2 : j.val < y_deg + 1 := j.isLt
                       have h3 : (y_deg + 1) * i.val + j.val < (x_deg + 1) * (y_deg + 1) := by
                         have : (y_deg + 1) * i.val + j.val < (y_deg + 1) * (i.val + 1) := by
                           simp [Nat.mul_add, Nat.add_assoc]
                           exact Nat.add_lt_add_left h2 _
                         have : (y_deg + 1) * (i.val + 1) ≤ (x_deg + 1) * (y_deg + 1) := by
                           apply Nat.mul_le_mul_right
                           exact Nat.succ_le_iff.mpr h1
                         exact Nat.lt_of_lt_of_le ‹(y_deg + 1) * i.val + j.val < (y_deg + 1) * (i.val + 1)› this
                       exact h3⟩ = 
                     (coeff_matrix.get i).get j) ∧
                   -- Matrix-vector multiplication gives polynomial evaluation
                   ∀ point_idx : Fin n,
                   (List.range ((x_deg + 1) * (y_deg + 1))).foldl (fun acc k =>
                     acc + (result.get point_idx).get ⟨k, by
                       have : k ∈ List.range ((x_deg + 1) * (y_deg + 1)) := by
                         exact List.mem_range.mpr (Nat.lt_succ_self ((x_deg + 1) * (y_deg + 1) - 1))
                       have : k < (x_deg + 1) * (y_deg + 1) := by
                         cases' Nat.eq_zero_or_pos ((x_deg + 1) * (y_deg + 1)) with h h
                         · rw [h] at *
                           simp [List.range] at this
                         · have : k < (x_deg + 1) * (y_deg + 1) := by
                             by_cases hk : k < (x_deg + 1) * (y_deg + 1)
                             · exact hk
                             · have : k ≥ (x_deg + 1) * (y_deg + 1) := Nat.le_of_not_gt hk
                               rw [List.mem_range] at this
                               exact False.elim (this this)
                           exact this
                       exact this⟩ * 
                     flattened_coeff.get ⟨k, by
                       have : k < (x_deg + 1) * (y_deg + 1) := by
                         by_cases hk : k < (x_deg + 1) * (y_deg + 1)
                         · exact hk
                         · have : k ∈ List.range ((x_deg + 1) * (y_deg + 1)) := by
                             exact List.mem_range.mpr (Nat.lt_succ_self ((x_deg + 1) * (y_deg + 1) - 1))
                           rw [List.mem_range] at this
                           exact False.elim (Nat.not_lt.mp hk this)
                       exact this⟩
                   ) 0 = 
                   -- Equivalent to direct 2D polynomial evaluation  
                   (List.range (x_deg + 1)).foldl (fun acc_i i =>
                     acc_i + (List.range (y_deg + 1)).foldl (fun acc_j j =>
                       acc_j + (coeff_matrix.get ⟨i, by
                         have : i < x_deg + 1 := by
                           by_cases hi : i < x_deg + 1
                           · exact hi
                           · have : i ∈ List.range (x_deg + 1) := by
                               exact List.mem_range.mpr (Nat.lt_succ_self (x_deg))
                             rw [List.mem_range] at this
                             exact False.elim (Nat.not_lt.mp hi this)
                         exact this⟩).get ⟨j, by
                         have : j < y_deg + 1 := by
                           by_cases hj : j < y_deg + 1
                           · exact hj
                           · have : j ∈ List.range (y_deg + 1) := by
                               exact List.mem_range.mpr (Nat.lt_succ_self (y_deg))
                             rw [List.mem_range] at this
                             exact False.elim (Nat.not_lt.mp hj this)
                         exact this⟩ * 
                       -- Note: hermite_basis exists from above, this is evaluation at point
                       1.0  -- Placeholder for correct hermite evaluation
                     ) 0
                   ) 0) ∧
                 -- Vandermonde matrix properties for polynomial fitting
                 (n ≥ (x_deg + 1) * (y_deg + 1) → 
                   -- Full rank condition for overdetermined systems
                   ∃ rank_val : Nat, rank_val = (x_deg + 1) * (y_deg + 1) ∧
                   -- Matrix has full column rank for unique least squares solution
                   True) ∧
                 -- Basic symmetry when degrees are equal
                 (x_deg = y_deg → 
                   ∀ point_idx : Fin n, ∀ i j : Nat, i ≤ x_deg → j ≤ y_deg →
                   ∃ basis_idx1 basis_idx2 : Fin ((x_deg + 1) * (y_deg + 1)),
                   basis_idx1.val = (y_deg + 1) * i + j ∧
                   basis_idx2.val = (y_deg + 1) * j + i ∧
                   -- Swapping x and y coordinates gives related matrix structure
                   True) ∧
                 -- Orthogonality properties conceptually exist
                 (∀ i1 j1 i2 j2 : Nat, i1 ≤ x_deg → j1 ≤ y_deg → i2 ≤ x_deg → j2 ≤ y_deg →
                   -- HermiteE polynomials are orthogonal with Gaussian weight
                   (i1 ≠ i2 ∨ j1 ≠ j2) → True)⌝⦄ := by
  apply Id.return_ok
  simp [hermevander2d]
  constructor
  · -- Matrix dimensions
    intro point_idx
    rw [vector_get_ofFn, buildRow_size]
  constructor
  · -- Matrix entries follow HermiteE basis structure  
    use hermiteE
    constructor
    · -- Base case 0
      intro t
      exact hermiteE_base_0 t
    constructor
    · -- Base case 1
      intro t
      exact hermiteE_base_1 t
    constructor
    · -- Recurrence relation
      intro k hk1 hk2 t
      have : k + 1 ≥ 1 := Nat.succ_le_iff.mpr (Nat.zero_le k)
      cases' k with k'
      · simp [hermiteE]
      · rw [← hermiteE_recurrence k' t]
        simp [Nat.succ_eq_add_one]
    · -- Matrix entries computed correctly
      intro point_idx basis_idx
      let i := basis_idx.val / (y_deg + 1)
      let j := basis_idx.val % (y_deg + 1)
      use i, j
      constructor
      · -- i ≤ x_deg
        have h1 : basis_idx.val < (x_deg + 1) * (y_deg + 1) := basis_idx.isLt
        have h2 : y_deg + 1 > 0 := Nat.succ_pos y_deg
        have h3 : i < x_deg + 1 := Nat.div_lt_iff_lt_mul_left h2 |>.mpr h1
        exact Nat.le_of_lt_succ h3
      constructor
      · -- j ≤ y_deg
        have h1 : j < y_deg + 1 := Nat.mod_lt basis_idx.val (Nat.succ_pos y_deg)
        exact Nat.le_of_lt_succ h1
      constructor
      · -- basis_idx.val = (y_deg + 1) * i + j
        simp [i, j]
        rw [Nat.div_add_mod]
      · -- Matrix entry correctness
        rw [vector_get_ofFn, buildRow_get]
        simp [i, j, computeEntry]
  constructor
  · -- Polynomial evaluation equivalence
    intro coeff_matrix
    use Vector.ofFn (fun k => 
      let i := k / (y_deg + 1)
      let j := k % (y_deg + 1)
      (coeff_matrix.get ⟨i, by
        have h1 : k < (x_deg + 1) * (y_deg + 1) := k.isLt
        have h2 : y_deg + 1 > 0 := Nat.succ_pos y_deg
        have h3 : i < x_deg + 1 := Nat.div_lt_iff_lt_mul_left h2 |>.mpr h1
        exact h3⟩).get ⟨j, by
        have h1 : j < y_deg + 1 := Nat.mod_lt k.val (Nat.succ_pos y_deg)
        exact h1⟩)
    constructor
    · -- Coefficient flattening
      intro i j
      simp [vector_get_ofFn]
      have h1 : (y_deg + 1) * i.val + j.val < (x_deg + 1) * (y_deg + 1) := by
        have : (y_deg + 1) * i.val + j.val < (y_deg + 1) * (i.val + 1) := by
          simp [Nat.mul_add, Nat.add_assoc]
          exact Nat.add_lt_add_left j.isLt _
        have : (y_deg + 1) * (i.val + 1) ≤ (x_deg + 1) * (y_deg + 1) := by
          apply Nat.mul_le_mul_right
          exact Nat.succ_le_iff.mpr i.isLt
        exact Nat.lt_of_lt_of_le ‹(y_deg + 1) * i.val + j.val < (y_deg + 1) * (i.val + 1)› this
      have h2 : (y_deg + 1) * i.val + j.val / (y_deg + 1) = i.val := by
        rw [Nat.add_mul_div_left _ _ (Nat.succ_pos y_deg)]
        simp [Nat.div_eq_zero_iff_lt]
        exact Nat.le_of_lt_succ j.isLt
      have h3 : (y_deg + 1) * i.val + j.val % (y_deg + 1) = j.val := by
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt j.isLt
      rw [h2, h3]
    · -- Matrix-vector multiplication equivalence
      intro point_idx
      simp
  constructor
  · -- Vandermonde matrix properties
    intro h
    use (x_deg + 1) * (y_deg + 1)
    constructor
    · rfl
    · trivial
  constructor
  · -- Symmetry properties
    intro h point_idx i j hi hj
    have h1 : (y_deg + 1) * i + j < (x_deg + 1) * (y_deg + 1) := by
      rw [h] at *
      have : (y_deg + 1) * i + j < (y_deg + 1) * (i + 1) := by
        simp [Nat.mul_add, Nat.add_assoc]
        exact Nat.add_lt_add_left (Nat.lt_succ_of_le hj) _
      have : (y_deg + 1) * (i + 1) ≤ (y_deg + 1) * (x_deg + 1) := by
        apply Nat.mul_le_mul_left
        exact Nat.succ_le_iff.mpr (Nat.lt_succ_of_le hi)
      exact Nat.lt_of_lt_of_le ‹(y_deg + 1) * i + j < (y_deg + 1) * (i + 1)› this
    have h2 : (y_deg + 1) * j + i < (x_deg + 1) * (y_deg + 1) := by
      rw [h] at *
      have : (y_deg + 1) * j + i < (y_deg + 1) * (j + 1) := by
        simp [Nat.mul_add, Nat.add_assoc]
        exact Nat.add_lt_add_left (Nat.lt_succ_of_le hi) _
      have : (y_deg + 1) * (j + 1) ≤ (y_deg + 1) * (x_deg + 1) := by
        apply Nat.mul_le_mul_left
        exact Nat.succ_le_iff.mpr (Nat.lt_succ_of_le hj)
      exact Nat.lt_of_lt_of_le ‹(y_deg + 1) * j + i < (y_deg + 1) * (j + 1)› this
    use ⟨(y_deg + 1) * i + j, h1⟩, ⟨(y_deg + 1) * j + i, h2⟩
    constructor
    · rfl
    constructor
    · rfl
    · trivial
  · -- Orthogonality properties
    intro i1 j1 i2 j2 h1 h2 h3 h4 h5
    trivial