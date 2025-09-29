// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_int_abs_nonneg(x: int)
    ensures
        int_abs(x) >= 0,
{
    if x >= 0 {
        assert(int_abs(x) == x);
    } else {
        assert(int_abs(x) == -x);
    }
}
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
    x
}
// </vc-code>


}
fn main() {}