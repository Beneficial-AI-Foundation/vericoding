// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix type mismatch for k */
proof fn is_prime(n: usize) -> (result: bool)
    requires n < usize::MAX,
    ensures result <==> is_prime_number(n as int)
{
    if n < 2 { return false; }
    let n_int = n as int;
    if n_int % 2 == 0 && n_int != 2 { return false; }

    let mut k: usize = 3;
    while (k * k) <= n
        invariant
            2 <= k,
            k % 2 == 1,
            k <= n / k + 1, // This invariant is not directly used for correctness but might be for loop termination
            forall|i: int| #![trigger (n_int % i)] 2 <= i < k as int ==> (n_int % i) != 0,
            // loop body ensures that k is incremented by 2
            // and thus k remains odd if it starts as odd
            k as int <= n_int,
        decreases n - k
    {
        if n_int % k as int == 0 { return false; }
        k = k + 2;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
fn prime_length(s: Vec<char>) -> (result: bool)
    ensures result <==> is_prime_number(s@.len() as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): pass `s.len()` as `usize` to `is_prime` */
{
    is_prime(s.len())
}
// </vc-code>


}

fn main() {}