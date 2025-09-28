// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error in `usize` increment */
proof fn is_prime(n: usize) -> (result: bool)
    requires
        n < usize::MAX,
    ensures
        result <==> is_prime_number(n as int),
{
    if n < 2 {
        return false;
    }
    let mut i: usize = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i as int ==> n as int % k != 0,
        decreases (n - i) as nat
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn prime_length(s: Vec<char>) -> (result: bool)
    ensures result <==> is_prime_number(s@.len() as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error in `usize` increment */
{
    let n = s.len();
    if n < 2 {
        return false;
    }
    let mut i: usize = 2;
    while i < n
        invariant
            s.len() == n,
            n >= 2,
            2 <= i <= n,
            forall|k: int| 2 <= k < i as int ==> n as int % k != 0,
        decreases (n - i) as nat
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>


}

fn main() {}