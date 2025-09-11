// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mcontained(v: &[i32], w: &[i32], n: usize, m: usize) -> (b: bool)
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}