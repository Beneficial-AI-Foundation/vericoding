import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def legendre_poly : Nat → Float → Float
| 0, _ => 1
| 1, x => x
| n + 2, x => 
  let l_n := legendre_poly (n + 1) x
  let l_n_minus_1 := legendre_poly n x
  ((2 * (n + 1 : Float) + 1) * x * l_n - (n + 1 : Float) * l_n_minus_1) / (n + 2 : Float)

-- LLM HELPER
def vector_map_with_index {α β : Type} {n : Nat} (f : Fin n → α → β) (v : Vector α n) : Vector β n :=
  Vector.mk (List.mapIdx (fun i a => f ⟨i, by simp [List.length_mapIdx]; exact v.2 ▸ Nat.lt_of_succ_le (Nat.succ_le_of_lt (List.length_pos_of_ne_nil (fun h => by simp [h] at v.2)))⟩ a) v.toList) (by simp [List.length_mapIdx]; exact v.2)

-- LLM HELPER
def vector_replicate {α : Type} (n : Nat) (a : α) : Vector α n :=
  Vector.mk (List.replicate n a) (by simp [List.length_replicate])

/-- Pseudo-Vandermonde matrix of given degree based on Legendre polynomials.
    Returns the pseudo-Vandermonde matrix of degree `deg` and sample points `x`.
    The pseudo-Vandermonde matrix is defined by V[..., i] = L_i(x) where 0 <= i <= deg.
    L_i represents the i-th Legendre polynomial. -/
def legvander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  return Vector.mk (List.map (fun xi => 
    Vector.mk (List.map (fun j => legendre_poly j xi) (List.range (deg + 1))) (by simp [List.length_map, List.length_range])
  ) x.toList) (by simp [List.length_map]; exact x.2)

-- LLM HELPER
lemma deg_pos_implies_one_lt_succ : ∀ deg : Nat, deg > 0 → 1 < deg + 1 := by
  intro deg h
  omega

/-- Specification: legvander constructs a pseudo-Vandermonde matrix where each row 
    corresponds to a point and each column corresponds to a Legendre polynomial evaluation.
    The matrix satisfies basic properties of Legendre polynomials:
    - L_0(x) = 1 (first column is all ones)
    - L_1(x) = x (second column equals input values when deg > 0)
    - The matrix has the correct dimensions -/
theorem legvander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    legvander x deg
    ⦃⇓result => ⌜
      -- First column (L_0) is all ones
      (∀ i : Fin n, (result.get i).get ⟨0, Nat.zero_lt_succ deg⟩ = 1) ∧
      -- Second column (L_1) equals x values when deg > 0
      (deg > 0 → ∀ i : Fin n, (result.get i).get ⟨1, deg_pos_implies_one_lt_succ deg⟩ = x.get i) ∧
      -- Matrix has correct dimensions and well-defined values
      (∀ i : Fin n, ∀ j : Fin (deg + 1), ∃ val : Float, (result.get i).get j = val)
    ⌝⦄ := by
  simp [legvander, Std.Do.BasicMonad.map_pure, Id.map_id, Id.pure_eq]
  constructor
  · -- First column is all ones
    intro i
    simp [Vector.get, List.get_map, legendre_poly, Vector.toList, List.get_range]
  constructor
  · -- Second column equals x values when deg > 0
    intro h i
    simp [Vector.get, List.get_map, legendre_poly, Vector.toList, List.get_range]
  · -- Matrix has correct dimensions and well-defined values
    intro i j
    simp [Vector.get, List.get_map]
    use legendre_poly j.val (x.get i)
    rfl