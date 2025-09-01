/- 
{
  "name": "numpy.polynomial.chebyshev.Chebyshev",
  "category": "Chebyshev polynomials",
  "description": "A Chebyshev series class.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.chebyshev.Chebyshev.html",
  "doc": "A Chebyshev series class.\n\n    The Chebyshev class provides the standard Python numerical methods\n    '+', '-', '*', '//', '%', 'divmod', '**', and '()' as well as the\n    attributes and methods listed below.\n\n    Parameters\n    ----------\n    coef : array_like\n        Chebyshev coefficients in order of increasing degree, i.e.,\n        \`\`(1, 2, 3)\`\` gives \`\`1*T_0(x) + 2*T_1(x) + 3*T_2(x)\`\`.\n    domain : (2,) array_like, optional\n        Domain to use. The interval \`\`[domain[0], domain[1]]\`\` is mapped\n        to the interval \`\`[window[0], window[1]]\`\` by shifting and scaling.\n        The default value is [-1., 1.].\n    window : (2,) array_like, optional\n        Window, see \`domain\` for its use. The default value is [-1., 1.].\n    symbol : str, optional\n        Symbol used to represent the independent variable in string\n        representations of the polynomial expression, e.g. for printing.\n        The symbol must be a valid Python identifier. Default value is 'x'.\n\n        .. versionadded:: 1.24",
  "type": "class"
}
-/

/-  Create a Chebyshev polynomial from coefficients with default domain and window [-1, 1] -/

/-  Specification: Creating a Chebyshev polynomial preserves coefficients and sets default domain/window -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Structure representing a Chebyshev polynomial with coefficients and domain/window mapping -/
structure ChebyshevPoly (n : Nat) where
  /-- Coefficients of the Chebyshev polynomial in increasing degree order -/
  coef : Vector Float n
  /-- Domain interval [domain_min, domain_max] -/
  domain_min : Float := -1.0
  domain_max : Float := 1.0
  /-- Window interval [window_min, window_max] -/
  window_min : Float := -1.0
  window_max : Float := 1.0

-- <vc-helpers>
-- </vc-helpers>

def chebyshev {n : Nat} (coef : Vector Float n) : Id (ChebyshevPoly n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem chebyshev_spec {n : Nat} (coef : Vector Float n) :
    ⦃⌜True⌝⦄
    chebyshev coef
    ⦃⇓result => ⌜-- Coefficients are preserved
                 (∀ i : Fin n, result.coef.get i = coef.get i) ∧
                 -- Default domain is [-1, 1]
                 result.domain_min = -1.0 ∧
                 result.domain_max = 1.0 ∧
                 -- Default window is [-1, 1]
                 result.window_min = -1.0 ∧
                 result.window_max = 1.0 ∧
                 -- Domain interval is valid
                 result.domain_min < result.domain_max ∧
                 -- Window interval is valid
                 result.window_min < result.window_max⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
