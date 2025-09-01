use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn spec_prime_helper(p: int) -> bool {
    if p <= 1 {
        false
    } else if p == 2 {
        true
    } else {
        true
    }
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
    let mut a: u32 = 2;
    while ((a as u64) * (a as u64) * (a as u64) <= (x as u64))
    invariant
        x > 1,
        2 <= a,
        (a as u128) * (a as u128) * (a as u128) <= (u32::MAX as u128) * (u32::MAX as u128) * (u32::MAX as u128),
    {
        if x % a == 0 {
            let mut is_a_prime = true;
            if a <= 1 {
                is_a_prime = false;
            } else {
                let mut k_a: u32 = 2;
                while (k_a as u64) * (k_a as u64) <= (a as u64)
                    invariant
                        2 <= k_a,
                        (k_a as u64) * (k_a as u64) <= (u32::MAX as u64),
                        a > 0,
                        is_a_prime == (forall |l: u32| 2 <= l < k_a ==> a % l != 0),
                {
                    if a % k_a == 0 {
                        is_a_prime = false;
                        break;
                    }
                    k_a = k_a + 1;
                }
                assert(is_a_prime == spec_prime(a as int));
            }
            if is_a_prime {
                let x_div_a = x / a;
                let mut b: u32 = a;
                while ((b as u64) * (b as u64) <= (x_div_a as u64))
                    invariant
                        x > 1,
                        a > 0,
                        x % a == 0,
                        x_div_a == x / a,
                        a <= b,
                        (b as u64) * (b as u64) <= (u32::MAX as u64),
                        x_div_a > 0,
                {
                    if x_div_a % b == 0 {
                        let mut is_b_prime = true;
                        if b <= 1 {
                            is_b_prime = false;
                        } else {
                            let mut k_b: u32 = 2;
                            while (k_b as u64) * (k_b as u64) <= (b as u64)
                                invariant
                                    2 <= k_b,
                                    (k_b as u64) * (k_b as u64) <= (u32::MAX as u64),
                                    b > 0,
                                    is_b_prime == (forall |l: u32| 2 <= l < k_b ==> b % l != 0),
                            {
                                if b % k_b == 0 {
                                    is_b_prime = false;
                                    break;
                                }
                                k_b = k_b + 1;
                            }
                            assert(is_b_prime == spec_prime(b as int));
                        }

                        if is_b_prime {
                            let c = x_div_a / b;
                            if c >= b {
                                proof {
                                    assert(x == (a as u32) * (b as u32) * (c as u32)); // Trigger for x == a*b*c (for next line)
                                }
                                let mut is_c_prime = true;
                                if c <= 1 {
                                    is_c_prime = false;
                                } else {
                                    let mut k_c: u32 = 2;
                                    while (k_c as u64) * (k_c as u64) <= (c as u64)
                                        invariant
                                            2 <= k_c,
                                            (k_c as u64) * (k_c as u64) <= (u32::MAX as u64),
                                            c > 0,
                                            is_c_prime == (forall |l: u32| 2 <= l < k_c ==> c % l != 0),
                                    {
                                        if c % k_c == 0 {
                                            is_c_prime = false;
                                            break;
                                        }
                                        k_c = k_c + 1;
                                    }
                                    assert(is_c_prime == spec_prime(c as int));
                                }
                                if is_c_prime {
                                    return true;
                                }
                            }
                        }
                    }
                    b = b + 1;
                }
            }
        }
        a = a + 1;
    }
    return false;
}
// </vc-code>

fn main() {}
}