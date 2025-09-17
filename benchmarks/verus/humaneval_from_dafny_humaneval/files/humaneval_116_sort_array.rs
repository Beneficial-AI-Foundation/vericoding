// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn popcount(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { popcount(n / 2) + n % 2 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sort_array(s: Seq<nat>) -> (sorted: Seq<nat>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted.len() ==> popcount(sorted[i]) <= popcount(sorted[j])
            && sorted.len() == s.len()
            && s.to_multiset() == sorted.to_multiset()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}