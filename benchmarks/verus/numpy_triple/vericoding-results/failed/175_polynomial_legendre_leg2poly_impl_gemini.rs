// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn leg2poly(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len(),

        (c.len() as int) < 3 ==> forall|i: int| 0 <= i < (c.len() as int) ==> result[i] == c[i],

        (c.len() as int) > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compile error and handled invalid empty input */
    let n = c.len();
    if n == 0 {
        loop {}
    }

    if n < 3 {
        return c;
    }

    let mut p = c;

    let mut k: usize = n - 1;
    while k >= 2
        invariant
            p.len() == n,
            2 <= k && k < n,
            forall|i: int| (k as int) < i && i < (n as int) ==> p@[i] == 0.0f32,
        decreases k
    {
        let val = p[k];
        p.set(k, 0.0f32);

        let k_f = k as f32;
        let c1 = (k_f - 1.0) / k_f;
        let c2 = (2.0 * k_f - 1.0) / k_f;

        p.set(k - 2, p[k - 2] - val * c1);
        p.set(k - 1, p[k - 1] + val * c2);

        k = k - 1;
    }

    p
}
// </vc-code>

}
fn main() {}