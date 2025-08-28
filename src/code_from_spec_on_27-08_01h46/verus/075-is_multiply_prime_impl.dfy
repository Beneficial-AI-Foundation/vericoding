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
    if x == 0 || y == 0 || z == 0 {
        proof {
            assert(x * y * z == 0);
        }
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

proof fn lemma_exists_intro(x: u32, a: u32, b: u32, c: u32)
    requires
        spec_prime(a as int),
        spec_prime(b as int), 
        spec_prime(c as int),
        x == a * b * c,
    ensures
        exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
{
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
    for a in 2..x {
        if prime(a) {
            for b in 2..x {
                if prime(b) {
                    for c in 2..x {
                        if prime(c) {
                            let prod = checked_mul_thrice(a, b, c);
                            if prod.is_some() && prod.unwrap() == x {
                                proof {
                                    assert(spec_prime(a as int));
                                    assert(spec_prime(b as int));
                                    assert(spec_prime(c as int));
                                    assert(x == a * b * c);
                                    lemma_exists_intro(x, a, b, c);
                                }
                                return true;
                            }
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