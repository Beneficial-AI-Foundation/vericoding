// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn repeat<T: Copy>(a: Vec<T>, repeats: usize) -> (result: Vec<T>)
    requires repeats > 0,
    ensures
        result.len() == a.len() * repeats,
        forall|i: int| 0 <= i < result.len() ==> {
            let k = i / (repeats as int);
            0 <= k < a.len() && result[i] == a[k]
        },
        forall|k: int| 0 <= k < a.len() ==> forall|j: int| 0 <= j < repeats ==> {
            let idx = k * (repeats as int) + j;
            0 <= idx < result.len() && result[idx] == a[k]
        },
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}