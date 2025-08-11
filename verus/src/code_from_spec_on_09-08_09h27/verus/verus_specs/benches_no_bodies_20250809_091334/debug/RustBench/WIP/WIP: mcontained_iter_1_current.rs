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
    let mut i = 0;
    let mut j = 0;
    
    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            forall|k: int| 0 <= k < i ==> (
                exists|l: int| 0 <= l < m && v[k] == w[l]
            )
    {
        if v[i] == w[j] {
            i += 1;
            j += 1;
        } else if v[i] < w[j] {
            return false;
        } else {
            j += 1;
        }
    }
    
    i == n
}

fn main() {}
}