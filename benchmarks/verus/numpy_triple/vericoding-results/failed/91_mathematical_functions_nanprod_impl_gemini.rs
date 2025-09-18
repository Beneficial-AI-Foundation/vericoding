// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn product_rec(s: Seq<f32>, acc: f32) -> f32
    decreases s.len()
{
    if s.len() == 0 {
        acc
    } else {
        let first = s[0];
        let rest = s.subrange(1, s.len());
        if first != first { // NaN check
            product_rec(rest, acc)
        } else {
            product_rec(rest, acc * first)
        }
    }
}

spec fn product_of_non_nan_elements(a: Seq<f32>) -> f32 {
    product_rec(a, 1.0f32)
}
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
    let mut prod: f32 = 1.0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            product_of_non_nan_elements(a@) == product_rec(a@.subrange(i, a.len()), prod),
        decreases a.len() - i
    {
        let current = a[i];
        if !current.is_nan() {
            prod = prod * current;
        }
        i = i + 1;
    }
    prod
}
// </vc-code>

}
fn main() {}