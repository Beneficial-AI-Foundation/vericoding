use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
// </vc-spec>
// <vc-code>
{
    let original_n = n;
    let mut n = n;
    let mut largest_factor = 1;
    let mut f = 2;
    
    while f * f <= n
        invariant
            1 <= largest_factor <= original_n,
            f >= 2,
            n >= 1,
            original_n % n == 0,
            forall |k: int| 2 <= k < f ==> (n as int) % k != 0,
            largest_factor == 1 || (is_prime_pred(largest_factor) && (original_n as int) % (largest_factor as int) == 0)
    {
        if (n as int) % (f as int) == 0 {
            largest_factor = f;
            n = n / f;
        } else {
            f = f + 1;
        }
    }
    
    if n > 1 {
        largest_factor = n;
    }
    
    largest_factor
}
// </vc-code>

fn main() {}
}