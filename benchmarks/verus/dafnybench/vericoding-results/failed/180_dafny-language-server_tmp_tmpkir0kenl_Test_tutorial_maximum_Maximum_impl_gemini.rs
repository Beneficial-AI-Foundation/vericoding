// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn maximum(values: Seq<int>) -> (max: int)
    requires
        values.len() > 0,
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed the loop counter 'i' from ghost type 'nat' to exec type 'usize' to fix compilation error. */
    let mut max_so_far = values@[0];
    let mut i: usize = 1;
    while i < values.len() as usize
        invariant
            1 <= i && i <= values.len() as usize,
            values.subrange(0, i as int).contains(max_so_far),
            forall|j: int| 0 <= j < i as int ==> values@[j] <= max_so_far,
        decreases (values.len() as usize) - i
    {
        if values@[i as int] > max_so_far {
            max_so_far = values@[i as int];
        }
        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}