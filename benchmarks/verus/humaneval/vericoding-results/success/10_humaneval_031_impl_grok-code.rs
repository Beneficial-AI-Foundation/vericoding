// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool
{
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes needed */
// </vc-helpers>

// <vc-spec>
fn is_prime(n: i8) -> (result: bool)
    ensures result <==> is_prime_number(n as int)
// </vc-spec>
// <vc-code>

/* code modified by LLM (iteration 3): Removed incorrect assertion and added trigger to loop invariant to ensure verification */
{
    if n < 2 {
        return false;
    }
    let mut i: i32 = 2;
    while i < (n as i32)
        invariant
            n >= 2,
            2 <= i,
            i <= n as i32 + 1,
            forall |j: int| 2 <= j < i ==> #[trigger] ((n as int) % j) != 0,
        decreases ((n as i32) - i)
    {
        if (n as i32) % i == 0 {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>


}

fn main() {}