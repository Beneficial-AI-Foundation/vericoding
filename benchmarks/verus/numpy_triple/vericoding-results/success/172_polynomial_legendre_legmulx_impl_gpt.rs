// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple integer min helper */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn legmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        result[1] == c[0],
        true, // Polynomial coefficients exist (simplified)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): maintain stronger invariants and use view-based reasoning to relate elements */
    let n = c.len();
    let mut r: Vec<f32> = Vec::new();
    r.push(0.0f32);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == c.len(),
            (i as int) <= (n as int),
            r.len() == i + 1,
            r[0] == 0.0f32,
            forall |k: int| 0 <= k < i as int ==> r@[k + 1] == c@[k],
        decreases n - i
    {
        let xi = c[i];
        assert(xi == c@[i as int]);
        r.push(xi);
        i = i + 1;
    }
    proof {
        if n > 0 {
            assert(1 < r.len());
            assert(0 < c.len());
            assert(0 <= 0 && 0 < n as int);
            assert(r@[1] == c@[0]);
            assert(r[1] == c[0]);
        }
    }
    r
}
// </vc-code>

}
fn main() {}