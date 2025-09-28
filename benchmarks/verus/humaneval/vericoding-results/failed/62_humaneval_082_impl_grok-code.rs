// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): reimplemented is_prime using int to avoid arithmetic overflow, ensuring postcondition holds by checking divisors up to sqrt(n) */
fn is_prime(n: usize) -> (result: bool)
    requires n < usize::MAX,
    ensures result <==> is_prime_number(n as int)
{
    let ni = n as int;
    if ni < 2 {
        return false;
    }
    let mut i: int = 2;
    while i * i <= ni
        invariant
            i >= 2,
            forall |k: int| 2 <= k < i ==> #[trigger] (ni % k) != 0,
        decreases (ni - i + 1)
    {
        if ni % i == 0 {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
fn prime_length(s: Vec<char>) -> (result: bool)
    ensures result <==> is_prime_number(s@.len() as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): simplified by calling is_prime directly on s.len(), relying on the helper's verification */
{
    is_prime(s.len())
}
// </vc-code>


}

fn main() {}