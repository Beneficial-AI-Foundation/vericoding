// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn seq_index_eq_from_eq<T>(s1: Seq<T>, s2: Seq<T>, i: int)
    requires
        s1 == s2,
        0 <= i < s1.len(),
    ensures
        s1[i] == s2[i]
{
}

// </vc-helpers>

// <vc-spec>
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)

    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
// </vc-spec>
// <vc-code>
{
    let copied = arr.clone();
    copied
}
// </vc-code>

}
fn main() {}