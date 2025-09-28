// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unused helper function since wrapping arithmetic can be done in exec code */
// </vc-helpers>

// <vc-spec>
fn numpy_diff(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() >= 2,
    ensures 
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i + 1] as int - a[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing int casts and using wrapping arithmetic */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            i <= a.len() - 1,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result[j] as int == a[j + 1] as int - a[j] as int,
        decreases a.len() - 1 - i
    {
        let diff = a[i + 1].wrapping_sub(a[i]);
        result.push(diff);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}