// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed invariant preservation by asserting the new element correctly */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x[j] != x[j])
        decreases x.len() - i
    {
        let is_nan = x[i] != x[i];
        result.push(is_nan);
        assert(result[i as int] == is_nan);
        assert(result[i as int] == (x[i as int] != x[i as int]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}