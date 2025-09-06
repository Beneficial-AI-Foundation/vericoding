/- 
{
  "name": "numpy.polynomial.polyutils.mapparms",
  "category": "Polynomial utilities",
  "description": "Linear map parameters between domains.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polyutils.mapparms.html",
  "doc": "Linear map parameters between domains.\n\n    Return the parameters of the linear map \`\`offset + scale*x\`\` that maps\n    \`old\` to \`new\` such that \`\`old[i] -> new[i]\`\`, \`\`i = 0, 1\`\`.\n\n    Parameters\n    ----------\n    old, new : array_like\n        Domains. Each domain must (successfully) convert to a 1-d array\n        containing precisely two values.\n\n    Returns\n    -------\n    offset, scale : scalars\n        The map \`\`L(x) = offset + scale*x\`\` maps the first domain to the\n        second.\n\n    See Also\n    --------\n    getdomain, mapdomain\n\n    Notes\n    -----\n    Also works for complex numbers, and thus can be used to calculate the\n    parameters required to map any line in the complex plane to any other\n    line therein.\n\n    Examples\n    --------\n    >>> from numpy.polynomial import polyutils as pu\n    >>> pu.mapparms((-1,1),(-1,1))\n    (0.0, 1.0)\n    >>> pu.mapparms((1,-1),(-1,1))\n    (-0.0, -1.0)\n    >>> i = complex(0,1)\n    >>> pu.mapparms((-i,-1),(1,i))\n    ((1+1j), (1-0j))",
}
-/

/-  Linear map parameters between domains. 
    Returns the parameters of the linear map `offset + scale*x` that maps
    `old` to `new` such that `old[i] -> new[i]`, `i = 0, 1`. -/

/-  Specification: mapparms computes linear mapping parameters between domains.
    The returned offset and scale define a linear map L(x) = offset + scale*x
    that maps the old domain to the new domain. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def mapparms (old new : Vector Float 2) : Id (Float × Float) :=
  sorry

theorem mapparms_spec (old new : Vector Float 2) 
    (h_old_distinct : old.get ⟨0, by simp⟩ ≠ old.get ⟨1, by simp⟩) :
    ⦃⌜old.get ⟨0, by simp⟩ ≠ old.get ⟨1, by simp⟩⌝⦄
    mapparms old new
    ⦃⇓result => ⌜let (offset, scale) := result
                  let oldlen := old.get ⟨1, by simp⟩ - old.get ⟨0, by simp⟩
                  let newlen := new.get ⟨1, by simp⟩ - new.get ⟨0, by simp⟩
                  -- The linear map L(x) = offset + scale*x maps old domain to new domain
                  offset + scale * old.get ⟨0, by simp⟩ = new.get ⟨0, by simp⟩ ∧
                  offset + scale * old.get ⟨1, by simp⟩ = new.get ⟨1, by simp⟩ ∧
                  -- Mathematical relationships from numpy implementation
                  scale = newlen / oldlen ∧
                  offset = (old.get ⟨1, by simp⟩ * new.get ⟨0, by simp⟩ - old.get ⟨0, by simp⟩ * new.get ⟨1, by simp⟩) / oldlen⌝⦄ := by
  sorry
