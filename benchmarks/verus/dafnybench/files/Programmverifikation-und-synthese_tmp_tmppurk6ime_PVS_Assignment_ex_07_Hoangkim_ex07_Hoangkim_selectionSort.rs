// <vc-preamble>
use vstd::prelude::*;

verus! {

fn find_min(a: &[i32], lo: usize) -> (minIdx: usize)
    requires
        a.len() > 0,
        lo < a.len(),
    ensures
        lo <= minIdx < a.len(),
        forall|x: usize| lo <= x < a.len() ==> a[minIdx as int] <= a[x as int],
{
    assume(false);
    lo
}

spec fn sorted(a: Seq<i32>) -> bool {
    forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] <= a[i]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut [i32])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}