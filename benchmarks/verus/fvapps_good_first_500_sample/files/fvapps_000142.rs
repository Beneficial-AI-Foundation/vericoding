// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_prime(n: nat) -> bool {
    n >= 2 && forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}

fn min_steps(n: nat) -> (result: nat)
    requires n >= 1
    ensures 
        result >= 0 &&
        (n >= 2 ==> result <= n) &&
        (n == 1 ==> result == 0) &&
        (n == 2 ==> result == 2) &&
        (n == 4 ==> result == 4)
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
fn main() {
    // #eval min_steps 3
    // #eval min_steps 1  
    // #eval min_steps 9
}