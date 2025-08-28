#![crate_name = "mcontained"]

use vstd::prelude::*;

verus! {

spec fn strict_sorted(arr: &[i32]) -> bool {
    forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] < arr[l]
}

// <vc-helpers>
spec fn contains(w: &[i32], m: usize, value: i32) -> bool {
    exists|j: int| 0 <= j < m && w[j] == value
}

proof fn lemma_contains_transitive(w: &[i32], m: usize, value: i32, j: int)
    requires
        0 <= j < m,
        w[j] == value,
    ensures
        contains(w, m, value),
{
}

proof fn lemma_strict_sorted_implies_no_duplicates(arr: &[i32])
    requires
        strict_sorted(arr),
    ensures
        forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] != arr[l],
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
#[verifier::loop_isolation(false)]
fn mcontained(v: &[i32], w: &[i32], n: usize, m: usize) -> (b: bool)
    requires
        n <= m && n >= 0,
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
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut count: usize = 0;

    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            0 <= count <= i,
            forall|k: int| 0 <= k < i ==> contains(w, m, v[k]),
    {
        if v[i] == w[j] {
            lemma_contains_transitive(w, m, v[i], j as int);
            i = i + 1;
            j = j + 1;
            count = count + 1;
        } else if v[i] < w[j] {
            return false;
        } else {
            j = j + 1;
        }
    }

    count == n
}
// </vc-code>

fn main() {}
}