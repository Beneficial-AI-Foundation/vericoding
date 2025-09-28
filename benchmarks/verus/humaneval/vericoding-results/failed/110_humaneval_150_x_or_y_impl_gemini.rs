// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation errors by using fully qualified lemma names */
fn compute_is_prime(n: u8) -> (result: bool)
    ensures
        result == is_prime(n as nat),
{
    if n <= 1 {
        return false;
    }

    let mut i: u8 = 2;
    while i < n
        invariant
            (n as nat) > 1,
            2 <= i,
            i <= n,
            forall|k: nat| 2 <= k < (i as nat) ==> #[trigger] ((n as nat) % k) != 0,
        decreases n - i
    {
        if n % i == 0 {
            proof {
                vstd::arithmetic::prime::lemma_is_not_prime_is_witnessed(n as nat, i as nat);
            }
            return false;
        }
        i = i + 1;
    }

    proof {
        vstd::arithmetic::prime::lemma_prime_is_prime_if_no_factors(n as nat);
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn x_or_y(n: u8, x: i8, y: i8) -> (result: i8)
    ensures 
        is_prime(n as nat) ==> result == x,
        !is_prime(n as nat) ==> result == y,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no change, logic relies on helper function */
{
    if compute_is_prime(n) {
        x
    } else {
        y
    }
}
// </vc-code>


}

fn main() {}