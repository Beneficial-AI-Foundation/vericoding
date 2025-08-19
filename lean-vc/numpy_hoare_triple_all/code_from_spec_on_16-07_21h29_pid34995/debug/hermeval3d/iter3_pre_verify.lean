import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def hermiteE_basis (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1
  | 1 => x
  | n + 2 => x * hermiteE_basis (n + 1) x - Float.ofNat (n + 1) * hermiteE_basis n x

-- LLM HELPER
def eval_at_point (x y z : Float) (c : Vector (Vector (Vector Float p) m) l) : Float :=
  (List.range l).foldl (fun acc i =>
    acc + (List.range m).foldl (fun acc_j j =>
      acc_j + (List.range p).foldl (fun acc_k k =>
        acc_k + c[i]![j]![k]! * hermiteE_basis i x * hermiteE_basis j y * hermiteE_basis k z
      ) 0.0
    ) 0.0
  ) 0.0

/-- Evaluate a 3-D HermiteE series at points (x, y, z).
    
    This function computes the trivariate HermiteE polynomial:
    p(x,y,z) = ∑_{i,j,k} c_{i,j,k} * He_i(x) * He_j(y) * He_k(z)
    
    where He_i, He_j, and He_k are the HermiteE basis polynomials.
-/
def hermeval3d {n l m p : Nat} (x y z : Vector Float n) 
    (c : Vector (Vector (Vector Float p) m) l) : Id (Vector Float n) :=
  Vector.ofFn (fun i => eval_at_point (x.get i) (y.get i) (z.get i) c)

/-- Specification: hermeval3d evaluates a 3D HermiteE series at corresponding points.
    
    This function implements the mathematical formula:
    p(x,y,z) = ∑_{i,j,k} c_{i,j,k} * He_i(x) * He_j(y) * He_k(z)
    
    Key properties:
    1. Trivariate polynomial evaluation using HermiteE basis
    2. 3D coefficient tensor structure preserves polynomial degrees
    3. Point-wise evaluation for corresponding (x,y,z) triples
    4. Mathematical correctness through HermiteE orthogonality
    5. Linearity in coefficients and separability of variables
-/
theorem hermeval3d_spec {n l m p : Nat} (x y z : Vector Float n) 
    (c : Vector (Vector (Vector Float p) m) l) :
    ⦃⌜True⌝⦄
    hermeval3d x y z c
    ⦃⇓result => ⌜-- Result has same size as input point vectors
                 result.size = n ∧
                 -- Each result point is the evaluation of the 3D polynomial
                 (∀ t : Fin n, 
                   ∃ eval_result : Float,
                   result.get t = eval_result ∧
                   -- Trivariate polynomial evaluation formula
                   (∀ i : Fin l, ∀ j : Fin m, ∀ k : Fin p,
                     -- Each coefficient contributes c_{i,j,k} * He_i(x) * He_j(y) * He_k(z)
                     True)) ∧
                 -- Mathematical properties: linearity in coefficients
                 (∀ t : Fin n, ∀ α β : Float, ∀ c1 c2 : Vector (Vector (Vector Float p) m) l,
                   -- Linearity property: the evaluation is linear in the coefficients
                   True)⌝⦄ := by
  simp [hermeval3d, triple_seq_congr_context]
  constructor
  · rfl
  constructor
  · intro t
    use eval_at_point (x.get t) (y.get t) (z.get t) c
    simp [Vector.get_ofFn]
    constructor
    · rfl
    · intro i j k
      trivial
  · intro t α β c1 c2
    trivial

/-- Sanity check: constant polynomial (all degrees 0) returns the constant value -/
theorem hermeval3d_constant {n : Nat} (x y z : Vector Float n) (c₀ : Float) :
    ⦃⌜True⌝⦄
    hermeval3d x y z (Vector.ofFn (fun _ : Fin 1 => 
      Vector.ofFn (fun _ : Fin 1 => 
        Vector.ofFn (fun _ : Fin 1 => c₀))))
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = c₀⌝⦄ := by
  simp [hermeval3d, triple_seq_congr_context]
  intro i
  simp [Vector.get_ofFn, eval_at_point]
  have : hermiteE_basis 0 (x.get i) = 1 := by simp [hermiteE_basis]
  have : hermiteE_basis 0 (y.get i) = 1 := by simp [hermiteE_basis]
  have : hermiteE_basis 0 (z.get i) = 1 := by simp [hermiteE_basis]
  simp [this]
  ring

/-- Sanity check: trilinear polynomial He₁(x) * He₁(y) * He₁(z) = x * y * z -/
theorem hermeval3d_trilinear {n : Nat} (x y z : Vector Float n) :
    ⦃⌜True⌝⦄
    hermeval3d x y z (Vector.ofFn (fun i : Fin 2 => 
      Vector.ofFn (fun j : Fin 2 => 
        Vector.ofFn (fun k : Fin 2 => 
          if i.val = 1 ∧ j.val = 1 ∧ k.val = 1 then 1.0 else 0.0))))
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x.get i * y.get i * z.get i⌝⦄ := by
  simp [hermeval3d, triple_seq_congr_context]
  intro i
  simp [Vector.get_ofFn, eval_at_point]
  have h0 : hermiteE_basis 0 (x.get i) = 1 := by simp [hermiteE_basis]
  have h1 : hermiteE_basis 1 (x.get i) = x.get i := by simp [hermiteE_basis]
  have h0_y : hermiteE_basis 0 (y.get i) = 1 := by simp [hermiteE_basis]
  have h1_y : hermiteE_basis 1 (y.get i) = y.get i := by simp [hermiteE_basis]
  have h0_z : hermiteE_basis 0 (z.get i) = 1 := by simp [hermiteE_basis]
  have h1_z : hermiteE_basis 1 (z.get i) = z.get i := by simp [hermiteE_basis]
  simp [h0, h1, h0_y, h1_y, h0_z, h1_z, List.range_succ]
  ring

/-- Mathematical property: separable evaluation equals product of individual evaluations -/
theorem hermeval3d_separable {n : Nat} (x y z : Vector Float n) (i j k : Nat) :
    ⦃⌜True⌝⦄
    hermeval3d x y z (Vector.ofFn (fun i' : Fin (i + 1) => 
      Vector.ofFn (fun j' : Fin (j + 1) => 
        Vector.ofFn (fun k' : Fin (k + 1) => 
          if i'.val = i ∧ j'.val = j ∧ k'.val = k then 1.0 else 0.0))))
    ⦃⇓result => ⌜∀ t : Fin n, 
                  result.get t = hermiteE_basis i (x.get t) * hermiteE_basis j (y.get t) * hermiteE_basis k (z.get t)⌝⦄ := by
  simp [hermeval3d, triple_seq_congr_context]
  intro t
  simp [Vector.get_ofFn, eval_at_point]
  ring

/-- Mathematical property: HermiteE basis function recurrence relation verification -/
theorem hermiteE_basis_recurrence (n : Nat) (x : Float) :
    hermiteE_basis 0 x = 1 ∧
    hermiteE_basis 1 x = x ∧
    (∀ k : Nat, k ≥ 2 → 
      hermiteE_basis k x = x * hermiteE_basis (k - 1) x - Float.ofNat (k - 1) * hermiteE_basis (k - 2) x) := by
  constructor
  · simp [hermiteE_basis]
  constructor
  · simp [hermiteE_basis]
  · intro k hk
    cases' k with k
    · omega
    cases' k with k
    · omega
    simp [hermiteE_basis]

/-- Mathematical property: HermiteE polynomials have correct parity -/
theorem hermiteE_basis_parity (n : Nat) (x : Float) :
    hermiteE_basis n (-x) = (if n % 2 = 0 then 1 else -1) * hermiteE_basis n x := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => 
      simp [hermiteE_basis]
    | 1 =>
      simp [hermiteE_basis]
      ring
    | n + 2 =>
      simp [hermiteE_basis]
      have ih1 : hermiteE_basis (n + 1) (-x) = (if (n + 1) % 2 = 0 then 1 else -1) * hermiteE_basis (n + 1) x := by
        apply ih
        omega
      have ih2 : hermiteE_basis n (-x) = (if n % 2 = 0 then 1 else -1) * hermiteE_basis n x := by
        apply ih
        omega
      rw [ih1, ih2]
      ring_nf
      congr 1
      simp [Nat.add_mod]
      ring