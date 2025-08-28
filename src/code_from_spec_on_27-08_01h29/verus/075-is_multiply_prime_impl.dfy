use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn prime(p: u32) -> (ret: bool)
    ensures
        ret <==> spec_prime(p as int),
{
    if p <= 1 {
        return false;
    }
    for k in 2..p
        invariant
            forall|j: int| 1 < j < k ==> #[trigger] (p as int % j) != 0,
            k <= p,
    {
        if p % k == 0 {
            return false;
        }
    }
    true
}

fn checked_mul_thrice(x: u32, y: u32, z: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() ==> ret.unwrap() == x * y * z,
        ret.is_none() ==> x * y * z > u32::MAX,
{
    if (x == 0 || y == 0 || z == 0) {
        return Some(0);
    }
    assert(x > 0 && y > 0 && z > 0);
    let prod2 = x.checked_mul(y);
    if prod2.is_some() {
        let prod3 = prod2.unwrap().checked_mul(z);
        if prod3.is_some() {
            let ans = prod3.unwrap();
            assert(ans == x * y * z);
            Some(ans)
        } else {
            assert(x * y * z > u32::MAX);
            None
        }
    } else {
        broadcast use group_mul_properties;

        assert(x * y * z >= y * z);
        None
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
    for a in 2..x
        invariant
            forall|p: int, q: int, r: int| 
                spec_prime(p) && spec_prime(q) && spec_prime(r) && 
                p < a && x == p * q * r ==> false
    {
        if prime(a) && x % a == 0 {
            let remaining = x / a;
            if remaining > 1 {
                let remaining_bound = remaining;
                for b in 2..remaining_bound + 1
                    invariant
                        spec_prime(a as int),
                        x % a == 0,
                        remaining == x / a,
                        remaining > 1,
                        b <= remaining_bound + 1,
                        remaining_bound == remaining,
                        forall|p: int, q: int| 
                            spec_prime(p) && spec_prime(q) && 
                            2 <= p < b && #[trigger] ((remaining as int) % p) == 0 ==> (remaining as int) / p <= 1 || !spec_prime((remaining as int) / p)
                {
                    if prime(b) && remaining % b == 0 {
                        let c = remaining / b;
                        if c > 1 && prime(c) {
                            proof {
                                assert(spec_prime(a as int));
                                assert(spec_prime(b as int));
                                assert(spec_prime(c as int));
                                assert(remaining == b * c);
                                assert(x == a * remaining);
                                assert(x == a * (b * c));
                                assert(x == (a as int) * (b as int) * (c as int));
                            }
                            return true;
                        }
                    }
                }
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}