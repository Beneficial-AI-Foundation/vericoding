use vstd::prelude::*;

verus! {

//Problem01
//a)

//b)
//Problem04

fn find_min(a: &[i32], lo: usize) -> (minIdx: usize)
    requires
        a.len() > 0,
        lo < a.len(),
    ensures
        lo <= minIdx < a.len(),
        forall|x: usize| lo <= x < a.len() ==> a[minIdx as int] <= a[x as int],
{
    assume(false);
    lo // dummy return
}

//Problem02
spec fn sorted(a: Seq<i32>) -> bool {
    forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] <= a[i]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut [i32])
    //ensures multiset(a) == multiset(old(a))
    //ensures sorted(a@)
// </vc-spec>
// <vc-code>
{
}
// </vc-code>

//Problem03

fn main() {}

}