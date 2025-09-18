// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): increment bound for usize indices */
fn incr_bound(len: usize, i: usize)
    requires
        i < len,
    ensures
        i + 1 <= len,
{
    proof {
        assert(i < len);
        assert(i + 1 <= len);
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
/* code modified by LLM (iteration 5): use usize index and cast to int for Vec indexing */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: usize| j < i ==> a[j as int] != key,
        decreases a.len() - i
    {
        if a[i as int] == key {
            return i as i32;
        } else {
            incr_bound(a.len(), i);
            i = i + 1;
        }
    }
    return -1;
}
// </vc-code>

}
fn main() {}