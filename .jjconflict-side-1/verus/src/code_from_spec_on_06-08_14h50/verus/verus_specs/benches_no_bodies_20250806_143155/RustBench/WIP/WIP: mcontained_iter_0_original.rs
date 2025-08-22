#![crate_name = "mcontained"]

use vstd::prelude::*;

verus! {

spec fn strict_sorted(arr: &[i32]) -> bool {
    forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] < arr[l]
}

#[verifier::loop_isolation(false)]
fn mcontained(v: &[i32], w: &[i32], n: usize, m: usize) -> (b: bool)
    requires
        n <= m && n>= 0,
        strict_sorted(v),
        strict_sorted(w),
        v.len() >= n && w.len() >= m
    ensures
        b ==> (forall|k: int| #![trigger v[k]]
            0 <= k < n ==> (
                exists|j: int| #![trigger w[j]]
                0 <= j < m && v[k] == w[j]
            ))
{
    return false;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
