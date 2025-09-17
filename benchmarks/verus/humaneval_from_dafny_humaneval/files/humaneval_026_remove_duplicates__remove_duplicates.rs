// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: Seq<int>) -> (result: Seq<int>)
    requires 
        forall|i: int| 0 <= i < a.len() ==> count_rec(a, a[i]) >= 1
    ensures 
        forall|i: int| 0 <= i < result.len() ==> count_rec(a, result[i]) == 1,
        forall|i: int| 0 <= i < a.len() ==> (result.contains(a[i]) <==> count_rec(a, a[i]) == 1)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}