// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}

/* helper modified by LLM (iteration 5): changed forall to use u64 instead of nat to avoid cast in trigger expression */
exec fn is_prime_impl(n: u64) -> (result: bool)
    ensures
        n as nat <= 1 ==> !result,
        n as nat > 1 ==> (result <==> is_prime(n as nat)),
{
    if n <= 1 {
        return false;
    }
    let mut k: u64 = 2;
    while k * k <= n
        invariant
            2 <= k,
            forall|m: u64| (2 <= m < k) ==> #[trigger] (n % m) != 0,
        decreases (n + 1 - k),
    {
        if n % k == 0 {
            return false;
        }
        k += 1;
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
/* code modified by LLM (iteration 5): implemented the function by calling the helper to check primality and return x or y accordingly */
{
    let prime = is_prime_impl(n as u64);
    if prime { x } else { y }
}
// </vc-code>


}

fn main() {}