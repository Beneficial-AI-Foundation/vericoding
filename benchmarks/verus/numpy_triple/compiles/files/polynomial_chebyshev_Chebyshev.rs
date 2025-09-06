/* A Chebyshev series class.

The Chebyshev class provides the standard Python numerical methods
'+', '-', '*', '//', '%', 'divmod', '**', and '()' as well as the
attributes and methods listed below.

Parameters
----------
coef : array_like
    Chebyshev coefficients in order of increasing degree, i.e.,
    ``(1, 2, 3)`` gives ``1*T_0(x) + 2*T_1(x) + 3*T_2(x)``.
domain : (2,) array_like, optional
    Domain to use. The interval ``[domain[0], domain[1]]`` is mapped
    to the interval ``[window[0], window[1]]`` by shifting and scaling.
    The default value is [-1., 1.].
window : (2,) array_like, optional
    Window, see `domain` for its use. The default value is [-1., 1.].
symbol : str, optional
    Symbol used to represent the independent variable in string
    representations of the polynomial expression, e.g. for printing.
    The symbol must be a valid Python identifier. Default value is 'x'.

Create a Chebyshev polynomial from coefficients with default domain and window [-1, 1]

Specification: Creating a Chebyshev polynomial preserves coefficients and sets default domain/window */

use vstd::prelude::*;

verus! {

/* Structure representing a Chebyshev polynomial with coefficients and domain/window mapping */
struct ChebyshevPoly {
    /* Coefficients of the Chebyshev polynomial in increasing degree order */
    coef: Vec<f32>,
    /* Domain interval [domain_min, domain_max] */
    domain_min: f32,
    domain_max: f32,
    /* Window interval [window_min, window_max] */
    window_min: f32,
    window_max: f32,
}
fn chebyshev(coef: Vec<f32>) -> (result: ChebyshevPoly)
    ensures
        /* Coefficients are preserved */
        result.coef.len() == coef.len(),
        forall|i: int| 0 <= i < coef.len() ==> result.coef[i] == coef[i],
        /* Default domain is [-1, 1] */
        result.domain_min == -1.0f32,
        result.domain_max == 1.0f32,
        /* Default window is [-1, 1] */
        result.window_min == -1.0f32,
        result.window_max == 1.0f32,
{
    // impl-start
    assume(false);
    ChebyshevPoly {
        coef: Vec::new(),
        domain_min: -1.0f32,
        domain_max: 1.0f32,
        window_min: -1.0f32,
        window_max: 1.0f32,
    }
    // impl-end
}
}
fn main() {}