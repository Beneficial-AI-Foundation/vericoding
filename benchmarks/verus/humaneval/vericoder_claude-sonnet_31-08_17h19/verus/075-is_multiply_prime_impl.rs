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
    while i < 65536 && (i as u64) * (i as u64) <= (n as u64)
        invariant
            3 <= i,
            i % 2 == 1,
            forall|k: int| 2 <= k < i ==> #[trigger] ((n as int) % k) != 0,
        decreases 65536 - i
    {
        if n % i == 0 {
            return false;
        }
        i += 2;
    }
    
    true
}

fn integer_cube_root_approx(x: u32) -> (result: u32)
    requires x > 1
    ensures result >= 2 && result <= 1000
{
    if x <= 8 { 2 } 
    else if x <= 27 { 3 } 
    else if x <= 64 { 4 } 
    else if x <= 125 { 5 }
    else if x <= 216 { 6 }
    else if x <= 343 { 7 }
    else if x <= 512 { 8 }
    else if x <= 729 { 9 }
    else if x <= 1000 { 10 }
    else { 100 }
}

fn integer_sqrt_approx(x: u32) -> (result: u32)
    requires x > 1
    ensures result >= 2 && result <= 1000
{
    if x <= 4 { 2 }
    else if x <= 9 { 3 }
    else if x <= 16 { 4 }
    else if x <= 25 { 5 }
    else if x <= 36 { 6 }
    else if x <= 49 { 7 }
    else if x <= 64 { 8 }
    else if x <= 81 { 9 }
    else if x <= 100 { 10 }
    else { 100 }
}

fn check_three_prime_factors(x: u32) -> (result: bool)
    requires x > 1
    ensures result <==> exists|a: int, b: int, c: int|
        spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c
{
    let mut a = 2u32;
    let cube_root_approx = integer_cube_root_approx(x);
    
    while a <= cube_root_approx && a <= 1000
        invariant
            2 <= a <= 1001,
            forall|p: int, q: int, r: int| 
                2 <= p < a && spec_prime(p) && spec_prime(q) && spec_prime(r) && x == p * q * r ==> false,
        decreases 1001 - a
    {
        if x % a == 0 && trial_division_prime_check(a) {
            let remaining = x / a;
            if remaining > 1 {
                let mut b = 2u32;
                let sqrt_approx = integer_sqrt_approx(remaining);
                
                while b <= sqrt_approx && b <= 1000 && b <= remaining
                    invariant
                        2 <= b <= 1001,
                        remaining == x / a,
                        remaining > 1,
                        spec_prime(a as int),
                        (a as int) * (remaining as int) == x as int,
                        forall|q: int, r: int| 
                            2 <= q < b && spec_prime(q) && spec_prime(r) && remaining == q * r ==> false,
                    decreases 1001 - b
                {
                    if remaining % b == 0 && trial_division_prime_check(b) {
                        let c = remaining / b;
                        if c > 1 && c <= u32::MAX && trial_division_prime_check(c) {
                            proof {
                                assert((b as int) * (c as int) == remaining as int);
                                assert((a as int) * (remaining as int) == x as int);
                                assert((a as int) * (b as int) * (c as int) == x as int);
                                assert(spec_prime(a as int) && spec_prime(b as int) && spec_prime(c as int));
                            }
                            return true;
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