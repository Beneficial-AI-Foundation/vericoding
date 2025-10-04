// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_different_arrays(n: nat, m: nat, k: nat, a: Vec<nat>) -> (result: nat)
    requires 
        n >= 1,
        m >= 1, 
        k >= 1,
        a.len() == n,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 1 && a[i] <= m,
    ensures
        1 <= result && result <= 1000000007,
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