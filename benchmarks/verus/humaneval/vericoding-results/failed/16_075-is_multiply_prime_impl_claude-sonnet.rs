// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed overflow checking, loop bounds, and invariants */
spec fn is_prime_u32(p: u32) -> bool {
    p > 1 && forall|k: u32| 1 < k < p ==> #[trigger] (p % k) != 0
}

fn check_prime(p: u32) -> (result: bool)
    requires p > 1
    ensures result <==> is_prime_u32(p)
{
    if p <= 3 {
        return p >= 2;
    }
    let mut i: u32 = 2;
    while i <= 46340 && i * i <= p
        invariant
            2 <= i,
            i <= 46341,
            forall|k: u32| 2 <= k < i ==> #[trigger] (p % k) != 0,
        decreases 46341 - i
    {
        if p % i == 0 {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)

    requires
        x > 1,

    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced for-loops with while-loops to avoid continue issue */
    let mut a: u32 = 2;
    while a < x {
        if check_prime(a) && x % a == 0 {
            let remaining = x / a;
            let mut b: u32 = 2;
            while b <= remaining {
                if check_prime(b) && remaining % b == 0 {
                    let c = remaining / b;
                    if c > 1 && check_prime(c) && a * b * c == x {
                        return true;
                    }
                }
                b = b + 1;
            }
        }
        a = a + 1;
    }
    false
}
// </vc-code>

}
fn main() {}