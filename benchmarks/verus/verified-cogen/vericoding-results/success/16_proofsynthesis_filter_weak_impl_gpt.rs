// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn is_multiple_of_3_u64(n: u64) -> bool { n % 3 == 0 }
proof fn lemma_multiple_of_3_implies_mod_zero(n: u64) ensures is_multiple_of_3_u64(n) ==> n % 3 == 0 { }
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
// </vc-spec>
// <vc-code>
{
    y.truncate(0);
}
// </vc-code>

}
fn main() {}