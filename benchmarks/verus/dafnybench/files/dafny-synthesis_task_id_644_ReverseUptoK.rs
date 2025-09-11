// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn array_index(v: Seq<i32>, i: int) -> i32 {
    v[i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse_upto_k(s: &mut Vec<i32>, k: usize)
    requires 
        2 <= k,
        k <= old(s).len(),
    ensures 
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < k ==> array_index(s@, i) == array_index(old(s)@, k - 1 - i),
        forall|i: int| k <= i < s.len() ==> array_index(s@, i) == array_index(old(s)@, i),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}