// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): noop helper to satisfy placeholder */
proof fn helpers_noop() { }

// </vc-helpers>

// <vc-spec>
spec fn product_of_non_nan_elements(a: Seq<f32>) -> f32 {
    arbitrary()
}

fn nanprod(a: Vec<f32>) -> (result: f32)
    ensures result == product_of_non_nan_elements(a@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute product skipping NaNs with loop and simple bounds invariant */
    let mut i: int = 0;
    let n: int = a.len() as int;
    let mut prod: f32 = 1.0;
    while i < n
        invariant
            0 <= i,
            i <= n,
        decreases
            n - i
    {
        let v: f32 = a[i as usize];
        if !v.is_nan() {
            prod = prod * v;
        }
        i = i + 1;
    }
    prod
}
// </vc-code>

}
fn main() {}