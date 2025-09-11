// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: Seq<int>) -> bool {
    forall|i: int| 1 <= i < a.len() ==> #[trigger] a[i] >= a[i-1]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_min(a: &[int], lo: usize) -> (minIdx: usize)
    requires 
        a.len() > 0,
        lo < a.len(),
    ensures 
        lo <= minIdx < a.len(),
        forall|x: int| lo <= x < a.len() ==> a[minIdx as int] <= a[x],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}