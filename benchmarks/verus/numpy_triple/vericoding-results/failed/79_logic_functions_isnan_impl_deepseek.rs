// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed Vec sequence indexing with @ operator */
fn f64_is_nan(f: f64) -> (b: bool) 
    ensures 
        b == (f != f),
{
    f != f
}
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
/* code modified by LLM (iteration 5): Fixed Vec sequence indexing with @ operator */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant 
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] == true <==> x@[j] != x@[j]),
        decreases x.len() - i,
    {
        let isnan_val = f64_is_nan(x@[i]);
        result.push(isnan_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}