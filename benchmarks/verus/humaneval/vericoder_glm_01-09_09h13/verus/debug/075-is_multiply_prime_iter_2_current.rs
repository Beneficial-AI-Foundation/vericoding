use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn is_prime(n: u32) -> (result: bool)
    requires
        n >= 2,
    ensures
        result <==> spec_prime(n as int),
{
    let mut i = 2;
    while i * i <= n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> n % k != 0,
    {
        if n % i == 0 {
            return false;
        }
        i += 1;
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
    let mut a = 2;
    while a * a * a <= x
        invariant
            a >= 2,
            forall|a0: int, b0: int, c0: int| 
                #[trigger] spec_prime(a0) && #[trigger] spec_prime(b0) && #[trigger] spec_prime(c0) && a0 * b0 * c0 == (x as int) 
                ==> a0 >= a as int,
    {
        if x % a == 0 {
            if is_prime(a) {
                let x1 = x / a;
                let mut b = a;
                while b * b <= x1
                    invariant
                        b >= a,
                        forall|a0: int, b0: int, c0: int| 
                            #[trigger] spec_prime(a0) && #[trigger] spec_prime(b0) && #[trigger] spec_prime(c0) && a0 * b0 * c0 == (x as int) && a0 == a as int
                            ==> b0 >= b as int,
                {
                    if x1 % b == 0 {
                        if is_prime(b) {
                            let c = x1 / b;
                            if c >= b && is_prime(c) {
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
}
// </vc-code>

fn main() {}
}