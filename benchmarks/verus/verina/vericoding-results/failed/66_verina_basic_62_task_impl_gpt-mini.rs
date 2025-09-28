// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): trivial proof helper to satisfy placeholder */
proof fn helper_stub() {
    proof {
    }
}
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use usize loop index and spec int-indexing in invariants */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int && i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> a[j] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            return i as i32;
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}