// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): converted to exec mode and fixed primality checking */
fn is_prime(n: usize) -> (result: bool)
    requires n < usize::MAX,
    ensures result <==> is_prime_number(n as int)
{
    if n < 2 {
        return false;
    }
    
    let mut k: usize = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k as int ==> #[trigger] ((n as int) % j) != 0,
        decreases n - k
    {
        if n % k == 0 {
            return false;
        }
        k = k + 1;
    }
    
    true
}
// </vc-helpers>

// <vc-spec>
fn prime_length(s: Vec<char>) -> (result: bool)
    ensures result <==> is_prime_number(s@.len() as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call is_prime helper function */
    let len = s.len();
    is_prime(len)
}
// </vc-code>


}

fn main() {}