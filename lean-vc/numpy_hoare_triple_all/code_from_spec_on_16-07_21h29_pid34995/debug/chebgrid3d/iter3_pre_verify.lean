import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic

open Std.Do

-- LLM HELPER
def chebyshev_T : Nat → Float → Float
| 0, _ => 1
| 1, x => x
| n+1, x => 2 * x * chebyshev_T n x - chebyshev_T (n-1) x

-- LLM HELPER
def compute_triple_sum_simple {ni nj nk : Nat} (f : Fin ni → Fin nj → Fin nk → Float) : Float :=
  if ni = 0 then 0
  else if nj = 0 then 0
  else if nk = 0 then 0
  else
    let rec sum_all (i : Nat) (acc : Float) : Float :=
      if hi : i ≥ ni then acc
      else
        let rec sum_j (j : Nat) (acc_j : Float) : Float :=
          if hj : j ≥ nj then acc_j
          else
            let rec sum_k (k : Nat) (acc_k : Float) : Float :=
              if hk : k ≥ nk then acc_k
              else
                let val := f ⟨i, Nat.lt_of_not_ge hi⟩ ⟨j, Nat.lt_of_not_ge hj⟩ ⟨k, Nat.lt_of_not_ge hk⟩
                sum_k (k + 1) (acc_k + val)
            let acc_j_new := sum_k 0 0
            sum_j (j + 1) (acc_j + acc_j_new)
        let acc_i_new := sum_j 0 0
        sum_all (i + 1) (acc + acc_i_new)
    sum_all 0 0

/-- Evaluate a 3-D Chebyshev series on the Cartesian product of x, y, and z.

    This function returns the values:
    p(a,b,c) = ∑_{i,j,k} c_{i,j,k} * T_i(a) * T_j(b) * T_k(c)

    where the points (a, b, c) consist of all triples formed by taking
    a from x, b from y, and c from z. The resulting points form
    a grid with x in the first dimension, y in the second, and z in
    the third. -/
def chebgrid3d {nx ny nz : Nat} {ni nj nk : Nat}
    (x : Vector Float nx) (y : Vector Float ny) (z : Vector Float nz)
    (c : Vector (Vector (Vector Float nk) nj) ni) :
    Id (Vector (Vector (Vector Float nz) ny) nx) :=
  Id.pure $ Vector.ofFn fun ix =>
    Vector.ofFn fun iy =>
      Vector.ofFn fun iz =>
        compute_triple_sum_simple fun i j k =>
          ((c.get i).get j).get k * 
          chebyshev_T i.val (x.get ix) *
          chebyshev_T j.val (y.get iy) *
          chebyshev_T k.val (z.get iz)

-- LLM HELPER
lemma compute_triple_sum_simple_ext {ni nj nk : Nat} (f g : Fin ni → Fin nj → Fin nk → Float) 
    (h : ∀ i j k, f i j k = g i j k) : 
    compute_triple_sum_simple f = compute_triple_sum_simple g := by
  simp [compute_triple_sum_simple]
  split_ifs with h_ni h_nj h_nk
  · rfl
  · rfl  
  · rfl
  · congr
    ext i j k
    exact h i j k

/-- Specification: chebgrid3d evaluates a 3D Chebyshev series on the Cartesian product.
    The result at position (ix, iy, iz) is the sum over all coefficient indices (i, j, k)
    of c[i][j][k] * T_i(x[ix]) * T_j(y[iy]) * T_k(z[iz]) where T_n is the n-th
    Chebyshev polynomial.
    
    Mathematical properties:
    1. The output has the correct shape: nx × ny × nz
    2. Each element is computed as a triple sum over the coefficient indices
    3. The function evaluates the 3D Chebyshev series at each grid point
    4. For a zero coefficient array, the result is zero everywhere
    5. The result is linear in the coefficients
    6. The Chebyshev polynomials T_i satisfy the recurrence relation:
       T_0(x) = 1, T_1(x) = x, T_{n+1}(x) = 2x*T_n(x) - T_{n-1}(x)
    7. The evaluation respects the orthogonality of Chebyshev polynomials on [-1, 1]
    8. When all x, y, z values are in [-1, 1], the series converges uniformly
    9. The result is the tensor product of 1D Chebyshev evaluations -/
theorem chebgrid3d_spec {nx ny nz : Nat} {ni nj nk : Nat}
    (x : Vector Float nx) (y : Vector Float ny) (z : Vector Float nz)
    (c : Vector (Vector (Vector Float nk) nj) ni)
    (chebyshev_T : Nat → Float → Float)
    (h_T0 : ∀ x, chebyshev_T 0 x = 1)
    (h_T1 : ∀ x, chebyshev_T 1 x = x)
    (h_Tn : ∀ n x, n ≥ 1 → chebyshev_T (n + 1) x = 2 * x * chebyshev_T n x - chebyshev_T (n - 1) x) :
    ⦃⌜True⌝⦄
    chebgrid3d x y z c
    ⦃⇓result => ⌜∀ (ix : Fin nx) (iy : Fin ny) (iz : Fin nz),
        ∃ (value : Float), 
        ((result.get ix).get iy).get iz = value ∧
        (∀ (compute_sum : (Fin ni → Fin nj → Fin nk → Float) → Float),
          (∀ f g, (∀ i j k, f i j k = g i j k) → compute_sum f = compute_sum g) →
          value = compute_sum (fun i j k => 
            ((c.get i).get j).get k * 
            chebyshev_T i.val (x.get ix) *
            chebyshev_T j.val (y.get iy) *
            chebyshev_T k.val (z.get iz)))⌝⦄ := by
  simp [Triple.spec_bind, Triple.spec_pure, chebgrid3d]
  intro ix iy iz compute_sum h_ext
  use compute_triple_sum_simple fun i j k =>
    ((c.get i).get j).get k * 
    chebyshev_T i.val (x.get ix) *
    chebyshev_T j.val (y.get iy) *
    chebyshev_T k.val (z.get iz)
  constructor
  · simp [Vector.get_ofFn]
  · exact h_ext _ _ compute_triple_sum_simple_ext