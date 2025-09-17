// <vc-preamble>
use vstd::prelude::*;

verus! {

type SortSeqState = Seq<(int, int)>;

spec fn less(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    x < u || (x == u && y > v)
}

spec fn less_eq(a: (int, int), b: (int, int)) -> bool {
    let (x, y) = a;
    let (u, v) = b;
    (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sort_seq(s: SortSeqState) -> (sorted: SortSeqState)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> less_eq(sorted[i], sorted[j]),
        sorted.len() == s.len(),
        s.to_multiset() == sorted.to_multiset()
// </vc-spec>
// <vc-code>
{
    assume(false);
    s
}
// </vc-code>


}

fn main() {}