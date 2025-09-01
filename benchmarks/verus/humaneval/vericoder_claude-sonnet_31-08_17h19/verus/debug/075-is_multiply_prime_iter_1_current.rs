use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
spec fn is_prime_factorization_of_three(x: int, a: int, b: int, c: int) -> bool {
    spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c
}

fn trial_division_prime_check(n: u32) -> (result: bool)
    requires n >= 2
    ensures result <==> spec_prime(n as int)
{
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }
    
    let mut i = 3;
    while i * i <= n
        invariant
            3 <= i,
            i % 2 == 1,
            forall|k: int| 2 <= k < i ==> #[trigger] ((n as int) % k) != 0,
        decreases n - i
    {
        if n % i == 0 {
            return false;
        }
        i += 2;
    }
    true
}

fn check_three_prime_factors(x: u32) -> (result: bool)
    requires x > 1
    ensures result <==> exists|a: int, b: int, c: int|
        spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c
{
    let mut a = 2;
    while a * a * a <= x
        invariant
            2 <= a,
            forall|p: int, q: int, r: int| 
                2 <= p < a && spec_prime(p) && spec_prime(q) && spec_prime(r) && x == p * q * r ==> false,
        decreases x - a
    {
        if x % a == 0 && trial_division_prime_check(a) {
            let remaining = x / a;
            let mut b = 2;
            while b * b <= remaining
                invariant
                    2 <= b,
                    remaining == x / a,
                    a * remaining == x,
                    spec_prime(a as int),
                    forall|q: int, r: int| 
                        2 <= q < b && spec_prime(q) && spec_prime(r) && remaining == q * r ==> false,
                decreases remaining - b
            {
                if remaining % b == 0 && trial_division_prime_check(b) {
                    let c = remaining / b;
                    if c > 1 && trial_division_prime_check(c) {
                        assert(x == a * b * c);
                        assert(spec_prime(a as int) && spec_prime(b as int) && spec_prime(c as int));
                        return true;
                    }
                }
                b += 1;
            }
        }
        a += 1;
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
    check_three_prime_factors(x)
}
// </vc-code>

fn main() {}
}