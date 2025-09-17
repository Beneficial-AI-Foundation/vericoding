// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(x: Seq<nat>, val: nat) -> nat {
    x.filter(|v: nat| v == val).len()
}

fn numpy_bincount(x: Vec<nat>, max_val: nat) -> (result: Vec<nat>)
    requires 
        forall|i: int| 0 <= i < x.len() ==> x[i] <= max_val,
    ensures
        result.len() == max_val + 1,
        forall|val: int| 0 <= val <= max_val ==> 
            result[val] == count_occurrences(x@, val as nat),
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