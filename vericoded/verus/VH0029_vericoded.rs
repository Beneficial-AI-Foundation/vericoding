// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool
{
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [added helper function for modulo trigger] */
spec fn mod_is_zero(a: int, b: int) -> bool {
    a % b == 0
}

/* helper modified by LLM (iteration 3): [reviewed, helper is correct] */
proof fn lemma_is_not_prime(n: int, k: int)
    requires
        n >= 2,
        2 <= k < n,
        n % k == 0,
    ensures !is_prime_number(n)
{
}

/* helper modified by LLM (iteration 5): [added lemma to prove primality from loop invariant] */
proof fn lemma_prove_is_prime(n: int)
    requires
        n >= 2,
        forall|j: int| 2 <= j < n ==> !mod_is_zero(n, j),
    ensures is_prime_number(n)
{
    assert forall|k: int| 2 <= k < n implies #[trigger] (n % k) != 0 by {
        assert(!mod_is_zero(n, k));
    }
    assert(is_prime_number(n));
}
// </vc-helpers>

// <vc-spec>
fn is_prime(n: i8) -> (result: bool)
    ensures result <==> is_prime_number(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [added proof block to satisfy postcondition] */
    if n < 2 {
        return false;
    }
    let mut k: i8 = 2;
    while k < n
        invariant
            n as int >= 2,
            2 <= k as int,
            k as int <= n as int,
            forall|j: int| 2 <= j < k as int ==> !mod_is_zero(n as int, j),
        decreases (n - k)
    {
        if n % k == 0 {
            proof {
                lemma_is_not_prime(n as int, k as int);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        lemma_prove_is_prime(n as int);
    }
    return true;
}
// </vc-code>


}

fn main() {}