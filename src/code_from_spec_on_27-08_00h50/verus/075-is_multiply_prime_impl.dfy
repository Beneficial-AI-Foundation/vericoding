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
        ret.is_some() ==> ret.unwrap() as int == x as int * y as int * z as int,
        ret.is_none() ==> x as int * y as int * z as int > u32::MAX,
{
    if x == 0 || y == 0 || z == 0 {
        return Some(0);
    }
    assert(x > 0 && y > 0 && z > 0);
    let prod2 = x.checked_mul(y);
    if prod2.is_some() {
        let prod3 = prod2.unwrap().checked_mul(z);
        if prod3.is_some() {
            let ans = prod3.unwrap();
            proof {
                assert(ans as int == x as int * y as int * z as int);
            }
            Some(ans)
        } else {
            proof {
                broadcast use group_mul_properties;
                assert(x as int * y as int * z as int > u32::MAX);
            }
            None
        }
    } else {
        proof {
            broadcast use group_mul_properties;
            assert(x as int * y as int * z as int > u32::MAX);
        }
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
                2 <= p < a && spec_prime(p) && spec_prime(q) && spec_prime(r) && p * q * r == x ==> false,
    {
        if prime(a) {
            for b in a..(x/a + 1)
                invariant
                    spec_prime(a as int),
                    b <= x/a + 1,
                    forall|q: int, r: int|
                        (a as int) <= q < b && spec_prime(q) && spec_prime(r) && (a as int) * q * r == x ==> false,
            {
                if b <= x / a && prime(b) && x % (a * b) == 0 {
                    let remainder = x / (a * b);
                    if remainder > 1 && remainder < x && prime(remainder) {
                        proof {
                            assert(spec_prime(a as int));
                            assert(spec_prime(b as int));
                            assert(spec_prime(remainder as int));
                            assert(x == (a as int) * (b as int) * (remainder as int));
                        }
                        return true;
                    }
                }
            }
        }
    }
    proof {
        assert(forall|p: int, q: int, r: int| 
            2 <= p < x && spec_prime(p) && spec_prime(q) && spec_prime(r) && p * q * r == x ==> false);
        if exists|a: int, b: int, c: int| spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c {
            let (a_wit, b_wit, c_wit) = choose|a: int, b: int, c: int| 
                spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c;
            assert(a_wit >= 2 && b_wit >= 2 && c_wit >= 2);
            let min_val = if a_wit <= b_wit && a_wit <= c_wit { a_wit }
                         else if b_wit <= a_wit && b_wit <= c_wit { b_wit }
                         else { c_wit };
            assert(min_val >= 2);
            assert(a_wit * b_wit * c_wit == x);
            assert(min_val * 2 * 2 <= a_wit * b_wit * c_wit);
            assert(min_val * 4 <= x);
            assert(min_val <= x / 4);
            assert(x > 4);
            assert(min_val < x);
            assert(false);
        }
    }
    false
}
// </vc-code>

}
fn main() {}