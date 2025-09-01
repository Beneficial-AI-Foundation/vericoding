use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn is_prime_u32(n: u32) -> (ret: bool)
    ensures ret <==> (n > 1 && forall|k: int| 1 < k < n as int ==> (n as int) % k != 0)
{
    if n < 2 {
        false
    } else if n == 2 {
        true
    } else if n % 2 == 0 {
        false
    } else {
        let mut i = 3;
        while i * i <= n {
            if n % i == 0 {
                return false;
            }
            i += 2;
        }
        true
    }
}

fn is_prime2(n: u32) -> (ret: bool)
    requires n >= 4,
    ensures ret <==> exists|b: int, c: int| spec_prime(b) && spec_prime(c) && n as int == b * c
{
    let mut b = 2;
    while u64::from(b) * u64::from(b) <= u64::from(n) {
        invariant u64::from(b) * u64::from(b) <= u64::from(n);
        if n % b == 0 {
            let c = n / b;
            if is_prime_u32(b) && is_prime_u32(c) {
                return true;
            }
        }
        b += 1;
    }
    false
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
    if x < 8 {
        false
    } else {
        let mut a = 2;
        while u64::from(a) * u64::from(a) * u64::from(a) <= u64::from(x) {
            invariant u64::from(a) * u64::from(a) * u64::from(a) <= u64::from(x);
            if x % a == 0 {
                let rest = x / a;
                if is_prime_u32(a) && is_prime2(rest) {
                    return true;
                }
            }
            a += 1;
        }
        false
    }
}
// </vc-code>

fn main() {}
}