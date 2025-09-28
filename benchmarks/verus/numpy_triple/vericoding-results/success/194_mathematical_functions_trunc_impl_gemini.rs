// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_trunc(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == x[i],
        forall|i: int| 0 <= i < result.len() ==> {
            /* Sign preservation */
            (x[i] > 0 ==> result[i] >= 0) &&
            (x[i] < 0 ==> result[i] <= 0) &&
            (x[i] == 0 ==> result[i] == 0)
        },
        forall|i: int| 0 <= i < result.len() ==> {
            /* Truncation moves towards zero (abs property) */
            int_abs(result[i] as int) <= int_abs(x[i] as int)
        }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(x.len());
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x[j],
        decreases x.len() - i
    {
        result.push(x[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}