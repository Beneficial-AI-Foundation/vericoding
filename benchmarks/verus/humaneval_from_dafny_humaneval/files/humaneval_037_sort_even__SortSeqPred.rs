// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Seq<int>, p: Seq<bool>) -> (sorted: Seq<int>)
    requires s.len() == p.len(),
    ensures 
        sorted.len() == s.len(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] <= sorted[j],
        s.to_multiset() == sorted.to_multiset(),
        forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}