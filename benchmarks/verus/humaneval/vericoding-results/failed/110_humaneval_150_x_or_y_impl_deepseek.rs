// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
proof fn helper_lemma(n: nat)
    ensures
        n > 1 && forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0 <==> is_prime(n),
{
    /* helper modified by LLM (iteration 5): Removed redundant proof and fixed equivalence */
    assert(n > 1 && forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0 ==> is_prime(n));
    assert(is_prime(n) ==> n > 1 && forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0);
}
// </vc-helpers>

// <vc-spec>
fn x_or_y(n: u8, x: i8, y: i8) -> (result: i8)
    ensures 
        is_prime(n as nat) ==> result == x,
        !is_prime(n as nat) ==> result == y,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added proper prime number checks with proof */
    proof {
        helper_lemma(n as nat);
    }
    
    if n > 1 {
        let is_prime_n = is_prime(n as nat);
        if is_prime_n {
            x
        } else {
            y
        }
    } else {
        y
    }
}
// </vc-code>


}

fn main() {}