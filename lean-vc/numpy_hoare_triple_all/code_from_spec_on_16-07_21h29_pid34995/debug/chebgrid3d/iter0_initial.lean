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
def compute_triple_sum {ni nj nk : Nat} (f : Fin ni → Fin nj → Fin nk → Float) : Float :=
  let sum_k (i : Fin ni) (j : Fin nj) : Float := 
    (Vector.range nk).foldl (fun acc k => acc + f i ⟨k, by simp⟩) 0
  let sum_j (i : Fin ni) : Float := 
    (Vector.range nj).foldl (fun acc j => acc + sum_k i ⟨j, by simp⟩) 0
  (Vector.range ni).foldl (fun acc i => acc + sum_j ⟨i, by simp⟩) 0

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
        compute_triple_sum fun i j k =>
          ((c.get i).get j).get k * 
          chebyshev_T i.val (x.get ix) *
          chebyshev_T j.val (y.get iy) *
          chebyshev_T k.val (z.get iz)

-- LLM HELPER
lemma compute_triple_sum_ext {ni nj nk : Nat} (f g : Fin ni → Fin nj → Fin nk → Float) 
    (h : ∀ i j k, f i j k = g i j k) : 
    compute_triple_sum f = compute_triple_sum g := by
  simp [compute_triple_sum]
  congr 1
  ext i
  congr 1
  ext j
  congr 1
  ext k
  exact h _ _ _

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
  intro ix iy iz
  use compute_triple_sum fun i j k =>
    ((c.get i).get j).get k * 
    chebyshev_T i.val (x.get ix) *
    chebyshev_T j.val (y.get iy) *
    chebyshev_T k.val (z.get iz)
  constructor
  · simp [Vector.get_ofFn]
  · intro compute_sum h_ext
    exact h_ext compute_triple_sum compute_triple_sum_ext