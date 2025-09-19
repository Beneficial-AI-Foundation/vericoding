// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn unique_elements(a: Seq<nat>) -> Set<nat>
    decreases a.len()
{
    if a.len() == 0 {
        set![]
    } else {
        unique_elements(a.skip(1)).insert(a[0])
    }
}
// </vc-helpers>

// <vc-spec>
fn subarrays_with_k_distinct(a: Vec<nat>, k: nat) -> (result: nat)
    requires 
        a.len() > 0,
        1 <= k <= 50,
        forall|x: nat| a@.contains(x) ==> 1 <= x <= 100,
    ensures 
        result >= 0,
        k == 1 ==> result >= a.len(),
        k == unique_elements(a@).len() ==> result >= 1,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}