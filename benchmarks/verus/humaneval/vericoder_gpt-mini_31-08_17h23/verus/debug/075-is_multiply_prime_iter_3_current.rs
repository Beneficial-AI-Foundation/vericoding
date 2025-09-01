use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn is_prime(n: int) -> bool
    requires
        n > 1,
    ensures
        result <==> spec_prime(n),
{
    let mut k: int = 2;
    while k < n
        invariant 2 <= k <= n,
        invariant { forall|j: int| 2 <= j < k ==> #[trigger]((n % j) != 0) },
        decreases n - k,
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
fn is_multiply_prime(x: u32) -> (ans: bool)
    // pre-conditions-start
    requires
        x > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let xi: int = x as int;

    let mut a: int = 2;
    while a <= xi
        invariant 2 <= a <= xi + 1,
        invariant { forall|a0: int| 2 <= a0 < a ==>
            !(exists|b: int, c: int|
                spec_prime(a0) && spec_prime(b) && spec_prime(c) && xi == a0 * b * c) },
        decreases xi + 1 - a,
    {
        if xi % a == 0 {
            if is_prime(a) {
                let m: int = xi / a;
                let mut b: int = 2;
                while b <= m
                    invariant 2 <= b <= m + 1,
                    invariant { forall|b0: int| 2 <= b0 < b ==>
                        !(spec_prime(a) && exists|c: int|
                            spec_prime(b0) && spec_prime(c) && xi == a * b0 * c) },
                    decreases m + 1 - b,
                {
                    if m % b == 0 {
                        if is_prime(b) {
                            let c: int = m / b;
                            if c > 1 && is_prime(c) {
                                return true;
                            }
                        }
                    }
                    b += 1;
                }
            }
        }
        a += 1;
    }

    false
    // impl-end
}
// </vc-code>

fn main() {}
}