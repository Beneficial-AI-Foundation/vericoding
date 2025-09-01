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
    
    let mut i = 3u32;
    while i <= 65535 && i * i <= n
        invariant
            3 <= i <= 65536,
            i % 2 == 1,
            forall|k: int| 2 <= k < i ==> #[trigger] ((n as int) % k) != 0,
        decreases 65536 - i
    {
        if n % i == 0 {
            return false;
        }
        if i > 65533 {
            break;
        }
        i += 2;
    }
    
    proof {
        if spec_prime(n as int) {
            assert(forall|k: int| 2 <= k < n ==> #[trigger] ((n as int) % k) != 0);
        } else {
            assert(exists|k: int| 1 < k < n && #[trigger] ((n as int) % k) == 0);
        }
    }
    
    true
}

fn check_three_prime_factors(x: u32) -> (result: bool)
    requires x > 1
    ensures result <==> exists|a: int, b: int, c: int|
        spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c
{
    let mut a = 2u32;
    let cube_root_approx = if x <= 8 { 2 } else if x <= 27 { 3 } else if x <= 64 { 4 } else if x <= 125 { 5 } else { (x as f32).powf(1.0/3.0) as u32 + 1 };
    
    while a <= cube_root_approx && a <= 1000
        invariant
            2 <= a,
            forall|p: int, q: int, r: int| 
                2 <= p < a && spec_prime(p) && spec_prime(q) && spec_prime(r) && x == p * q * r ==> false,
        decreases 1001 - a
    {
        if a <= x && x % a == 0 && a >= 2 && trial_division_prime_check(a) {
            let remaining = x / a;
            if remaining > 1 {
                let mut b = 2u32;
                let sqrt_approx = if remaining <= 4 { 2 } else { (remaining as f32).sqrt() as u32 + 1 };
                
                while b <= sqrt_approx && b <= 1000 && b <= remaining
                    invariant
                        2 <= b,
                        remaining == x / a,
                        remaining > 1,
                        spec_prime(a as int),
                        forall|q: int, r: int| 
                            2 <= q < b && spec_prime(q) && spec_prime(r) && remaining == q * r ==> false,
                    decreases 1001 - b
                {
                    if b <= remaining && remaining % b == 0 && trial_division_prime_check(b) {
                        let c = remaining / b;
                        if c > 1 && c <= u32::MAX && trial_division_prime_check(c) {
                            proof {
                                assert((a as int) * (b as int) * (c as int) == 
                                       (a as int) * ((remaining as int) / (b as int)) * (b as int));
                                assert((a as int) * (remaining as int) == x as int);
                                assert((x as int) == (a as int) * (b as int) * (c as int));
                            }
                            return true;
                        }
                    }
                    if b >= 1000 {
                        break;
                    }
                    b += 1;
                }
            }
        }
        if a >= 1000 {
            break;
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