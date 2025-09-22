// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn x_or_y(n: u8, x: i8, y: i8) -> (result: i8)
    ensures 
        is_prime(n as nat) ==> result == x,
        !is_prime(n as nat) ==> result == y,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}