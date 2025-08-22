use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
{
    let mut i: u32 = 2;
    while i < n
        invariant
            2 <= i <= n,
            /* code modified by LLM (iteration 2): added trigger annotation to fix quantifier inference error */
            forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases n - i
    {
        if n % i == 0 {
            return true;
        }
        i = i + 1;
    }
    return false;
}

fn main() {}
}