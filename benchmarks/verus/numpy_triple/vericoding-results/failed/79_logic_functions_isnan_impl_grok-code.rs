// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_nan(f: f64) -> bool { f != f }
// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant to use @[j] instead of .view()@[j] to resolve compilation error */
    let mut result: Vec<bool> = Vec::new();
    let length: usize = x.len();
    let mut i: usize = 0;
    while i < length
        invariant
            0 <= (i as int) <= (length as int),
            result.len() as int == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == (x@[j] != x@[j])
        decreases (length - i) as int
    {
        let is_nan_val = x[i] != x[i];
        result.push(is_nan_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}