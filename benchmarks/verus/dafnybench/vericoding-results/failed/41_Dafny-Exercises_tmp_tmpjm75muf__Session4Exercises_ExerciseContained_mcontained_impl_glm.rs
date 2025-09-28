use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mcontained(v: &[i32], w: &[i32], n: usize, m: usize) -> (b: bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
    requires 
        n <= m,
        n >= 0,
        strict_sorted(v@),
        strict_sorted(w@),
        v@.len() >= n,
        w@.len() >= m,
    ensures
        b == forall|k: int| 0 <= k < n ==> w@.subrange(0, m as int).contains(v@[k])
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let mut j = 0;
    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            forall|k: int| 0 <= k < (i as int) ==> w@.subrange(0, j as int).contains(v@[k]),
            i < n ==> (forall|k: int| 0 <= k < (j as int) ==> w@[k] < v@[i as int]),
        decreases (n - i) + (m - j),
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
// </vc-code>

fn main() {}

}