// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
// </vc-helpers>

// <vc-spec>
fn x_or_y(n: u8, x: i8, y: i8) -> (result: i8)
    ensures 
        is_prime(n as nat) ==> result == x,
        !is_prime(n as nat) ==> result == y,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected direct use of `n` in `is_prime` function by using `@n` to access its mathematical value in ghost context, ensuring type compatibility for verification. */
{
    if is_prime(@n as nat) {
        x
    } else {
        y
    }
}
// </vc-code>


}

fn main() {}