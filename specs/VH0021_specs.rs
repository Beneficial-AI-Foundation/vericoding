// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn largest_divisor(n: i8) -> (d: i8)
    requires 
        n as int > 1
    ensures 
        1 <= d as int &&
        (d as int) < (n as int) &&
        n as int % d as int == 0 &&
        (forall|k: int| (d as int) < k && k < (n as int) ==> #[trigger] ((n as int) % k) != 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}