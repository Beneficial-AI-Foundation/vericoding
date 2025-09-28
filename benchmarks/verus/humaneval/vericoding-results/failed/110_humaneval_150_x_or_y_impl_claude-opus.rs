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
    /* code modified by LLM (iteration 5): removed invalid invariant_except_break syntax */
    let mut prime = n > 1;
    if n > 1 {
        let mut k: u8 = 2;
        while k < n
            invariant
                2 <= k <= n,
                prime == (n > 1 && forall|j: nat| 2 <= j < k ==> #[trigger] ((n as nat) % j) != 0),
            decreases n - k
        {
            if n % k == 0 {
                prime = false;
                assert((n as nat) % (k as nat) == 0);
                break;
            }
            k = k + 1;
        }
        assert(prime == is_prime(n as nat));
    } else {
        assert(!is_prime(n as nat));
    }
    
    if prime {
        x
    } else {
        y
    }
}
// </vc-code>


}

fn main() {}