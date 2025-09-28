// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn linear_search_index_proof(a: Seq<i32>, e: i32, i: nat) -> (result: nat)
    requires
        i <= a.len(),
        forall|j: int| 0 <= j < i ==> a[j] != e,
    ensures
        result <= a.len(),
        result == a.len() || a[result as int] == e,
        forall|j: int| 0 <= j < result ==> a[j] != e,
    decreases a.len() - i,
{
    if i < a.len() {
        if a[i as int] == e {
            i
        } else {
            linear_search_index_proof(a, e, i + 1)
        }
    } else {
        i
    }
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
            forall|j: int| 0 <= j < i ==> a[j] != e,
        decreases a.len() - i,
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    a.len()
}
// </vc-code>

}
fn main() {}