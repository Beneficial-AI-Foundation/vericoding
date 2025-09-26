-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebgrid3d {nx ny nz : Nat} {ni nj nk : Nat}
    (x : Vector Float nx) (y : Vector Float ny) (z : Vector Float nz)
    (c : Vector (Vector (Vector Float nk) nj) ni) :
    Id (Vector (Vector (Vector Float nz) ny) nx) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
  sorry
-- </vc-theorems>