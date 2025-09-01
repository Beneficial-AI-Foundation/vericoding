use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn is_prime(n: int) -> (ret: bool)
requires n >= 2,
ensures ret <==> spec_prime(n)
{
    let mut k = 2;
    while k * k <= n
    invariant 2 <= k,
             forall|j: int| 2 <= j < k ==> n % j != 0
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
    let mut remaining = x as int;
    let mut count = 0;
    let mut i = 2;
    while i * i <= remaining
    invariant remaining >= 1,
             i >= 2
    {
        if remaining % i == 0 {
            if is_prime(i) {
                while remaining % i == 0
                invariant remaining >= 1, i >= 2
                {
                    remaining = remaining / i;
                    count += 1;
                }
            } else {
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    if remaining > 1 {
        if is_prime(remaining) {
            count += 1;
        }
    }
    assert(count >= 3 ==> exists|a: int, b: int, c: int| spec_prime(a) && spec_prime(b) && spec_prime(c) && x as int == a * b * c);
    count >= 3
}
// </vc-code>

fn main() {}
}