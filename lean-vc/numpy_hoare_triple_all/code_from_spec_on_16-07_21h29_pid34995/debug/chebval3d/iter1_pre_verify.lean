import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Chebyshev polynomial of the first kind T_n(x) -/
def chebyshev (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | n + 2 => 2.0 * x * chebyshev (n + 1) x - chebyshev n x

/-- Helper function to compute the 3D Chebyshev sum at a single point -/
def chebval3d_at_point (x y z : Float) {i j k : Nat} (c : Vector (Vector (Vector Float k) j) i) : Float :=
  let sum := (List.range i).foldl (fun acc_i ii =>
    acc_i + (List.range j).foldl (fun acc_j jj =>
      acc_j + (List.range k).foldl (fun acc_k kk =>
        acc_k + ((c.get ⟨ii, by simp; exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_of_mem_diff ⟨ii, rfl⟩)))⟩).get ⟨jj, by simp; exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_of_mem_diff ⟨jj, rfl⟩)))⟩).get ⟨kk, by simp; exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.mem_range.mp (List.mem_of_mem_diff ⟨kk, rfl⟩)))⟩ * chebyshev ii x * chebyshev jj y * chebyshev kk z
      ) 0.0
    ) 0.0
  ) 0.0
  sum

-- LLM HELPER
def chebval3d_at_point_simple (x y z : Float) {i j k : Nat} (c : Vector (Vector (Vector Float k) j) i) : Float :=
  let mut sum : Float := 0.0
  for ii in [0:i] do
    for jj in [0:j] do
      for kk in [0:k] do
        let coeff := ((c.get ⟨ii, by omega⟩).get ⟨jj, by omega⟩).get ⟨kk, by omega⟩
        sum := sum + coeff * chebyshev ii x * chebyshev jj y * chebyshev kk z
  sum

/-- Evaluate a 3-D Chebyshev series at points (x, y, z).
    
    This function evaluates the sum:
    p(x,y,z) = Σ_{i,j,k} c[i,j,k] * T_i(x) * T_j(y) * T_k(z)
    
    where T_n is the n-th Chebyshev polynomial of the first kind.
-/
def chebval3d {n : Nat} {i j k : Nat} (x y z : Vector Float n) (c : Vector (Vector (Vector Float k) j) i) : Id (Vector Float n) :=
  Id.pure (Vector.ofFn fun idx => chebval3d_at_point_simple (x.get idx) (y.get idx) (z.get idx) c)

-- LLM HELPER
lemma chebval3d_unfold {n : Nat} {i j k : Nat} (x y z : Vector Float n) (c : Vector (Vector (Vector Float k) j) i) :
    chebval3d x y z c = Id.pure (Vector.ofFn fun idx => chebval3d_at_point_simple (x.get idx) (y.get idx) (z.get idx) c) := by
  rfl

-- LLM HELPER
lemma chebval3d_at_point_equiv (x y z : Float) {i j k : Nat} (c : Vector (Vector (Vector Float k) j) i) :
    chebval3d_at_point x y z c = chebval3d_at_point_simple x y z c := by
  simp [chebval3d_at_point, chebval3d_at_point_simple]
  sorry

/-- Specification: chebval3d evaluates a 3-D Chebyshev polynomial series
    
    The function evaluates a 3D Chebyshev polynomial at each point (x[idx], y[idx], z[idx])
    using the coefficient tensor c.
    
    Key mathematical properties:
    1. The result has the same size as the input coordinate vectors
    2. Each element is computed independently using the corresponding x, y, z values
    3. The evaluation uses Chebyshev polynomials of the first kind
    4. Preserves the structure: if all coefficients are zero, the result is zero
    5. Linear in coefficients: scaling coefficients scales the result
-/
theorem chebval3d_spec {n : Nat} {i j k : Nat} (x y z : Vector Float n) (c : Vector (Vector (Vector Float k) j) i) :
    ⦃⌜True⌝⦄
    chebval3d x y z c
    ⦃⇓result => ⌜
        -- Size preservation
        result.size = n ∧
        -- Each element is computed using the 3D Chebyshev formula at that point
        (∀ idx : Fin n, result.get idx = chebval3d_at_point (x.get idx) (y.get idx) (z.get idx) c) ∧
        -- Zero coefficients yield zero result
        ((∀ ii : Fin i, ∀ jj : Fin j, ∀ kk : Fin k, 
            ((c.get ii).get jj).get kk = 0) → 
         (∀ idx : Fin n, result.get idx = 0)) ∧
        -- Linearity property: if we scale all coefficients by a factor α, 
        -- the result is scaled by the same factor
        (∀ α : Float, ∀ c_scaled : Vector (Vector (Vector Float k) j) i,
         (∀ ii : Fin i, ∀ jj : Fin j, ∀ kk : Fin k,
            ((c_scaled.get ii).get jj).get kk = α * ((c.get ii).get jj).get kk) →
         (∃ result_scaled : Vector Float n,
            chebval3d x y z c_scaled = pure result_scaled ∧
            ∀ idx : Fin n, result_scaled.get idx = α * result.get idx))
    ⌝⦄ := by
  simp [HoareTriple.wlp_bind, HoareTriple.wlp_pure, chebval3d_unfold]
  constructor
  · -- Size preservation
    simp [Vector.size_ofFn]
  constructor
  · -- Each element computed correctly
    intro idx
    simp [Vector.get_ofFn]
    rw [chebval3d_at_point_equiv]
  constructor
  · -- Zero coefficients yield zero result
    intro h_zero idx
    simp [Vector.get_ofFn, chebval3d_at_point_simple]
    sorry
  · -- Linearity property
    intro α c_scaled h_scale
    use Vector.ofFn fun idx => chebval3d_at_point_simple (x.get idx) (y.get idx) (z.get idx) c_scaled
    constructor
    · rfl
    · intro idx
      simp [Vector.get_ofFn, chebval3d_at_point_simple]
      sorry