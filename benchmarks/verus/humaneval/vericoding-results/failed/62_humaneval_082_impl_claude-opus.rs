// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
}
// </vc-preamble>

// <vc-helpers>
proof fn is_prime(n: usize) -> (result: bool)
    requires n < usize::MAX,
    ensures result <==> is_prime_number(n as int)
{
    /* helper modified by LLM (iteration 5): fixed arithmetic type error with proper usize addition */
    if n < 2 {
        return false;
    }
    
    if n == 2 {
        return true;
    }
    
    let mut k: usize = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> #[trigger] ((n as int) % j) != 0,
        decreases n - k
    {
        if n % k == 0 {
            return false;
        }
        k = k + 1;
    }
    
    assert(forall|j: int| 2 <= j < n ==> #[trigger] ((n as int) % j) != 0);
    true
}
// </vc-helpers>

// <vc-spec>
fn prime_length(s: Vec<char>) -> (result: bool)
    ensures result <==> is_prime_number(s@.len() as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call helper function to check primality */
    let len = s.len();
    let result = is_prime(len);
    result
}
// </vc-code>


}

fn main() {}