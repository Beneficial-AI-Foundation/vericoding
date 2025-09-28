// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_index_within_len(k: int, i: usize, len: usize)
    requires
        0 <= k < i,
        i <= len,
    ensures
        0 <= k < len
{
    assert(0 <= k);
    assert(k < len);
}
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    ensures
        result <= a.len(),
        result == a.len() || a[result as int] == e,
        forall|i: int| 0 <= i < result ==> a[i] != e,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    i
}
// </vc-code>

}
fn main() {}