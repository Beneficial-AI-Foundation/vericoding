// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): chebyshev coefficient for derivative */
spec fn cheb_coeff(j: int) -> int { if j == 0 { 1 } else if j == 1 { 4 } else { 2 * (j + 1) } }
// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i32>, scl: i32) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute derivative coefficients without calling spec helpers */
    let n = c.len() as int;
    let mut result = Vec::<i32>::new();
    let mut i: int = 0;
    while i < n - 1
        invariant 0 <= i && i <= n - 1
        invariant result.len() == (i as usize)
        decreases n - 1 - i
    {
        let coef_int: int = if i == 0 { 1 } else if i == 1 { 4 } else { 2 * (i + 1) };
        let coef = coef_int as i32;
        result.push(scl * coef * c[(i + 1) as usize]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}