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
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == x[j],
            forall|j: int| 0 <= j < i ==> {
                (x[j] > 0 ==> result[j] >= 0) &&
                (x[j] < 0 ==> result[j] <= 0) &&
                (x[j] == 0 ==> result[j] == 0)
            },
            forall|j: int| 0 <= j < i ==> {
                int_abs(result[j] as int) <= int_abs(x[j] as int)
            },
        decreases x.len() - i
    {
        result.push(x[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}