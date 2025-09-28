// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): avoid break by setting k = n when divisor found */
fn is_prime_check(n: u8) -> (res: bool)
    ensures
        res == is_prime(n as nat),
{
    let mut prime: bool = true;
    if n <= 1 {
        prime = false;
        proof {
            assert(!prime);
            assert(!is_prime(n as nat));
        }
    } else {
        let mut k: u8 = 2;
        while k < n
            invariant
                2 <= k,
                k <= n,
                prime == (forall|i: nat| 2 <= i < (k as nat) ==> #[trigger] ((n as nat) % i) != 0),
            decreases (n as nat) - (k as nat)
        {
            if (n % k) == 0 {
                prime = false;
                k = n;
            } else {
                k += 1;
            }
        }
        proof {
            if prime {
                assert(!(k < n));
                assert(k >= n);
                assert(forall|i: nat| 2 <= i < (n as nat) ==> #[trigger] ((n as nat) % i) != 0);
                assert(is_prime(n as nat));
            } else {
                assert(!is_prime(n as nat));
            }
        }
    }
    prime
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
    /* code modified by LLM (iteration 5): select x when n is prime, else y */
    let p = is_prime_check(n);
    let result: i8 = if p { x } else { y };
    result
}
// </vc-code>


}

fn main() {}