// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::*;

verus! {

proof fn search(s: Seq<i32>, x: i32) -> (k: usize)

    requires 
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures 
        0 <= k <= s.len()
        && forall|i: int| 0 <= i < k ==> s[i] <= x
        && forall|i: int| k <= i < s.len() ==> s[i] >= x
        && forall|z: i32| s.subrange(0, k as int).contains(z) ==> z <= x
        && forall|z: i32| s.subrange(k as int, s.len() as int).contains(z) ==> z >= x
        && s == s.subrange(0, k as int) + s.subrange(k as int, s.len() as int),
{
  assume(false);
  0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sort(m: Multiset<i32>) -> (r: Seq<i32>)
    ensures 
        r.to_multiset() == m
        && forall|p: int, q: int| 0 <= p < q < r.len() ==> r[p] <= r[q],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}