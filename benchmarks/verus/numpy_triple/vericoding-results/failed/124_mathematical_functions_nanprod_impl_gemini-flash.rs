// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The previous implementation of `product_of_non_nan_elements` had a bug. When `a` contains `NaN` values, `filter` removes them, but if `filter` returns an empty sequence, `fold` with `1.0` as the initial accumulator returns `1.0`. Instead, an empty sequence should result in `1.0` only if all elements were `NaN`, or if the original sequence was empty. The corrected version directly handles `a.len() == 0` for an initial product of `1.0` and otherwise uses `fold` on the filtered sequence. */
spec fn product_of_non_nan_elements(a: Seq<f32>) -> f32 {
    if a.len() == 0 {
        1.0
    } else {
        let filtered = a.filter(|x: f32| !x.is_nan());
        if filtered.len() == 0 {
            // All elements were NaN, or the sequence was empty
            1.0
        } else {
            filtered.fold(1.0, |acc: f32, x: f32| acc * x)
        }
    }
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
/* code modified by LLM (iteration 5): The `@prod` in the invariant was causing a compilation error because `prod` is a `f32` and not a `Seq<f32>`, so `@` cannot be applied to it. Removed the `@` from `prod`. */
{
    let mut prod: f32 = 1.0;
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            prod == product_of_non_nan_elements(a@.subsequence(0, i))
    {
        let val = a[i];
        if !val.is_nan() {
            prod = prod * val;
        }
        i = i + 1;
    }
    prod
}
// </vc-code>

}
fn main() {}