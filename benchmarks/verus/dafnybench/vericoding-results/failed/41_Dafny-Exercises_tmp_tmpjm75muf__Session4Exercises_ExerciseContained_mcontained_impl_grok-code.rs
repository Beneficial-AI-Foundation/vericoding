use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>
spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}
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
    let mut j: int = 0;
    let mut result = true;
    let mut k: int = 0;
    while k < n as int
        invariant
            0 <= k <= n as int,
            0 <= j <= m as int,
            result == forall|i: int| 0 <= i < k ==> exists|jj: int| 0 <= jj < m as int ==> w@[jj] == v@[i],  // equivalent to contains in subrange 0..m
    {
        while j < m as int && w@[j] < v@[k]
            invariant
                0 <= k <= n as int,
                0 <= j <= m as int,
                result == forall|i: int| 0 <= i < k ==> exists|jj: int| 0 <= jj < m as int ==> w@[jj] == v@[i],
                forall|jj: int| 0 <= jj < j ==> jj < m as int && w@[jj] < v@[k],
        {
            j += 1;
        }
        if j >= m as int || w@[j] != v@[k] {
            result = false;
        }
        k += 1;
    }
    result
}
// </vc-code>

fn main() {}

}