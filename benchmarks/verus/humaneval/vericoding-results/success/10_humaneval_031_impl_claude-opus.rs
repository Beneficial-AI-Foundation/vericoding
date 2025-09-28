// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool
{
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_prime(n: i8) -> (result: bool)
    ensures result <==> is_prime_number(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    if n < 2 {
        return false;
    }
    
    let mut k: i8 = 2;
    while k < n
        invariant
            2 <= n,
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> #[trigger] ((n as int) % j) != 0,
        decreases n - k
    {
        if n % k == 0 {
            assert((n as int) % (k as int) == 0);
            return false;
        }
        k = k + 1;
    }
    
    assert(k == n);
    assert(forall|j: int| 2 <= j < n ==> #[trigger] ((n as int) % j) != 0);
    true
}
// </vc-code>


}

fn main() {}