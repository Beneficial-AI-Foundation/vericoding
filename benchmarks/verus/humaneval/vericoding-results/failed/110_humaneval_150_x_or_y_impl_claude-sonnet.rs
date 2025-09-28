// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn is_even(n: nat) -> bool {
    n % 2 == 0
}

spec fn has_small_factor(n: nat) -> bool {
    exists|k: nat| 2 <= k <= 10 && k < n && #[trigger] (n % k) == 0
}

/* helper modified by LLM (iteration 5): removed problematic exists assertion */
proof fn lemma_small_composite_has_small_factor(n: nat)
    requires
        2 <= n <= 100,
        !is_prime(n),
    ensures
        has_small_factor(n),
{
    if n % 2 == 0 {
        assert(n % 2 == 0);
    } else if n % 3 == 0 {
        assert(n % 3 == 0);
    } else if n % 5 == 0 {
        assert(n % 5 == 0);
    } else if n % 7 == 0 {
        assert(n % 7 == 0);
    }
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
    /* code modified by LLM (iteration 5): removed trigger annotation issue */
    
    if n <= 1 {
        return y;
    }
    
    if n == 2 {
        return x;
    }
    
    if n % 2 == 0 {
        return y;
    }
    
    let mut i = 3u8;
    while i * i <= n
        invariant
            i >= 3,
            i % 2 == 1,
            forall|k: nat| 2 <= k < i ==> #[trigger] ((n as nat) % k) != 0,
        decreases 256 - i
    {
        if n % i == 0 {
            return y;
        }
        i = i + 2;
    }
    
    x
}
// </vc-code>


}

fn main() {}