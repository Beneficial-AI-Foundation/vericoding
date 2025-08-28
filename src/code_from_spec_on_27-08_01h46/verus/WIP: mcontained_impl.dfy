#![crate_name = "mcontained"]

use vstd::prelude::*;

verus! {

spec fn strict_sorted(arr: &[i32]) -> bool {
    forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] < arr[l]
}

// <vc-helpers>
spec fn contained_up_to(v: &[i32], w: &[i32], n: int, m: int, k: int) -> bool {
    forall|i: int| #![trigger v[i]] 0 <= i < k ==> (
        exists|j: int| #![trigger w[j]] 0 <= j < m && v[i] == w[j]
    )
}

proof fn lemma_contained_extend(v: &[i32], w: &[i32], n: int, m: int, k: int)
    requires
        0 <= k < n,
        contained_up_to(v, w, n, m, k),
        exists|j: int| 0 <= j < m && v[k] == w[j]
    ensures
        contained_up_to(v, w, n, m, k + 1)
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
{
    let mut i = 0;
    let mut j = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= m,
            contained_up_to(v, w, n as int, m as int, i as int),
            i < n ==> j < m,
            forall|k: int| #![trigger v[k]] 0 <= k < i ==> (
                exists|l: int| #![trigger w[l]] 0 <= l < m && v[k] == w[l]
            )
        decreases n - i
    {
        let mut found = false;
        let old_j = j;
        let mut witness_j = 0;
        
        while j < m && !found
            invariant
                old_j <= j <= m,
                i < n,
                found ==> (witness_j + 1 == j && v[i as int] == w[witness_j as int] && old_j <= witness_j < m),
                !found ==> forall|k: int| #![trigger w[k]] old_j <= k < j ==> v[i as int] != w[k],
                contained_up_to(v, w, n as int, m as int, i as int)
            decreases m - j
        {
            if v[i] == w[j] {
                found = true;
                witness_j = j;
                j = j + 1;
            } else if v[i] > w[j] {
                j = j + 1;
            } else {
                break;
            }
        }
        
        if !found {
            return false;
        }
        
        proof {
            assert(exists|k: int| 0 <= k < m && v[i as int] == w[k]);
            lemma_contained_extend(v, w, n as int, m as int, i as int);
        }
        
        i = i + 1;
    }
    
    true
}
// </vc-code>

fn main() {}
}