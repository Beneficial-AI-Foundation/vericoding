// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_not_in_prefix(a: Seq<i32>, e: i32, idx: int) -> bool {
    forall|j: int| 0 <= j < idx ==> a[j] != e
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
    let mut i = 0;
    while i < a.len()
        invariant
            is_not_in_prefix(a.view(), e, i as int),
            i <= a.len(),
            decreases a.len() as int - i as int
    {
        if a[i] == e {
            return i;
        }
        i += 1;
    }
    return a.len();
}
// </vc-code>

}
fn main() {}