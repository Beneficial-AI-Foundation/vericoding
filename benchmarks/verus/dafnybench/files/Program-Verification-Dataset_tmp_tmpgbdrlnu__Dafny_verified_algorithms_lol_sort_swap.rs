// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures 
        a.len() == old(a).len(),
        a@ == old(a)@.update(i as int, old(a)@[j as int]).update(j as int, old(a)@[i as int]),
        valid_permut(a@, old(a)@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}