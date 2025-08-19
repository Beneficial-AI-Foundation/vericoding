import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.polynomial.polyutils.mapdomain: Apply linear map to input points.

    The linear map `offset + scale*x` that maps the domain `old` to
    the domain `new` is applied to the points `x`.

    This function implements the mathematical transformation:
    x_out = new[0] + m(x - old[0])
    where m = (new[1] - new[0]) / (old[1] - old[0])

    Parameters:
    - x: Points to be mapped (Vector of Float values)
    - old: Two-element vector defining the old domain [old[0], old[1]]
    - new: Two-element vector defining the new domain [new[0], new[1]]

    Returns:
    - x_out: Array of points of the same shape as x, after linear transformation
-/
def mapdomain {n : Nat} (x : Vector Float n) (old new : Vector Float 2) : Id (Vector Float n) :=
  let scale := (new.get 1 - new.get 0) / (old.get 1 - old.get 0)
  let offset := new.get 0 - scale * old.get 0
  Vector.ofFn (fun i => offset + scale * x.get i)

/-- Specification: mapdomain applies linear transformation to map points from old domain to new domain.

    The function computes a linear transformation that maps the interval [old[0], old[1]] 
    to the interval [new[0], new[1]], then applies this transformation to each point in x.

    Mathematical properties:
    1. The transformation is linear: f(x) = offset + scale * x
    2. The scale factor is: (new[1] - new[0]) / (old[1] - old[0])
    3. The offset is: new[0] - scale * old[0]
    4. Points at old[0] map to new[0], points at old[1] map to new[1]

    Precondition: The old domain must be non-degenerate (old[1] ≠ old[0])
    Postcondition: Each result point follows the linear transformation formula
-/
theorem mapdomain_spec {n : Nat} (x : Vector Float n) (old new : Vector Float 2)
    (h_nondegenerate : old.get 1 ≠ old.get 0) :
    ⦃⌜old.get 1 ≠ old.get 0⌝⦄
    mapdomain x old new
    ⦃⇓result => ⌜∀ i : Fin n, 
      let scale := (new.get 1 - new.get 0) / (old.get 1 - old.get 0)
      let offset := new.get 0 - scale * old.get 0
      result.get i = offset + scale * x.get i⌝⦄ := by
  unfold mapdomain
  apply specReturn
  intro i
  simp [Vector.get_ofFn]