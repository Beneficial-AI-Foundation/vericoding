// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(ss: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<int>, b: Seq<int>) -> bool
    decreases a.len(), b.len()
{
    a.len() == b.len() && 
    ((a.len() == 0 && b.len() == 0) ||  
    exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && 
        a[i] == b[j] && 
        is_permutation(
            a.subrange(0, i) + (if i < a.len() { a.subrange(i + 1, a.len() as int) } else { seq![] }),
            b.subrange(0, j) + (if j < b.len() { b.subrange(j + 1, b.len() as int) } else { seq![] })
        ))
}

spec fn is_permutation2(a: Seq<int>, b: Seq<int>) -> bool {
    a.to_multiset() == b.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_min_index(a: &[int], s: usize, e: usize) -> (min_i: usize)
    requires
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}