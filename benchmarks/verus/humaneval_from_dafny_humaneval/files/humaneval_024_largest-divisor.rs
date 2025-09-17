// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn largest_divisor(n: int) -> (d: int)
    requires 
        n > 1
    ensures 
        1 <= d < n,
        n % d == 0,
        forall|k: int| d < k < n ==> #[trigger] (n % k) != 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}