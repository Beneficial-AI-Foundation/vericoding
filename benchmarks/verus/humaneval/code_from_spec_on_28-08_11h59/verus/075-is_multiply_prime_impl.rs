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
        ret.is_some() ==> ret.unwrap() as int == (x as int) * (y as int) * (z as int),
        ret.is_none() ==> (x as int) * (y as int) * (z as int) > u32::MAX,
{
    if (x == 0 || y == 0 || z == 0) {
        proof {
            if x == 0 {
                assert((x as int) * (y as int) * (z as int) == 0 * (y as int) * (z as int));
                assert(0 * (y as int) * (z as int) == 0);
            } else if y == 0 {
                assert((x as int) * (y as int) * (z as int) == (x as int) * 0 * (z as int));
                assert((x as int) * 0 * (z as int) == 0);
            } else {
                assert((x as int) * (y as int) * (z as int) == (x as int) * (y as int) * 0);
                assert((x as int) * (y as int) * 0 == 0);
            }
            assert((x as int) * (y as int) * (z as int) == 0);
        }
        return Some(0);
    }
    assert(x > 0 && y > 0 && z > 0);
    let prod2 = x.checked_mul(y);
    if prod2.is_some() {
        let prod3 = prod2.unwrap().checked_mul(z);
        if prod3.is_some() {
            let ans = prod3.unwrap();
            proof {
                assert(ans as int == (x as int) * (y as int) * (z as int));
            }
            Some(ans)
        } else {
            proof {
                broadcast use group_mul_properties;
                assert((x as int) * (y as int) * (z as int) > u32::MAX);
            }
            None
        }
    } else {
        proof {
            broadcast use group_mul_properties;
            assert((x as int) * (y as int) * (z as int) >= (y as int) * (z as int));
            assert((x as int) * (y as int) * (z as int) > u32::MAX);
        }
        None
    }
}

proof fn no_prime_factorization_helper(x: u32, max_a: u32)
    requires
        x > 1,
        max_a < x,
        forall|a1: int, b1: int, c1: int| 
            (2 <= a1 <= max_a && spec_prime(a1) && spec_prime(b1) && spec_prime(c1) && x == a1 * b1 * c1) ==> false,
    ensures
        forall|a1: int, b1: int, c1: int| 
            (2 <= a1 <= max_a && spec_prime(a1) && spec_prime(b1) && spec_prime(c1) && x == a1 * b1 * c1) ==> false,
{}
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
            forall|a1: int, b1: int, c1: int| 
                (2 <= a1 < a && spec_prime(a1) && spec_prime(b1) && spec_prime(c1) && x as int == a1 * b1 * c1) ==> false,
    {
        if prime(a) {
            for b in 2..x
                invariant
                    spec_prime(a as int),
                    forall|a1: int, b1: int, c1: int| 
                        (2 <= a1 < a && spec_prime(a1) && spec_prime(b1) && spec_prime(c1) && x as int == a1 * b1 * c1) ==> false,
                    forall|b1: int, c1: int| 
                        (2 <= b1 < b && spec_prime(b1) && spec_prime(c1) && x as int == (a as int) * b1 * c1) ==> false,
            {
                if prime(b) {
                    for c in 2..x
                        invariant
                            spec_prime(a as int),
                            spec_prime(b as int),
                            forall|a1: int, b1: int, c1: int| 
                                (2 <= a1 < a && spec_prime(a1) && spec_prime(b1) && spec_prime(c1) && x as int == a1 * b1 * c1) ==> false,
                            forall|b1: int, c1: int| 
                                (2 <= b1 < b && spec_prime(b1) && spec_prime(c1) && x as int == (a as int) * b1 * c1) ==> false,
                            forall|c1: int| 
                                (2 <= c1 < c && spec_prime(c1) && x as int == (a as int) * (b as int) * c1) ==> false,
                    {
                        if prime(c) {
                            let prod_opt = checked_mul_thrice(a, b, c);
                            if prod_opt.is_some() && prod_opt.unwrap() == x {
                                proof {
                                    assert(spec_prime(a as int));
                                    assert(spec_prime(b as int));
                                    assert(spec_prime(c as int));
                                    assert(prod_opt.unwrap() as int == (a as int) * (b as int) * (c as int));
                                    assert(x as int == (a as int) * (b as int) * (c as int));
                                }
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    proof {
        assert(forall|a1: int, b1: int, c1: int| 
            (2 <= a1 < x && spec_prime(a1) && spec_prime(b1) && spec_prime(c1) && x as int == a1 * b1 * c1) ==> false);
        
        if exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x as int == a * b * c {
            let a1 = choose|a: int, b: int, c: int| 
                spec_prime(a) && spec_prime(b) && spec_prime(c) && x as int == a * b * c;
            let b1 = choose|a: int, b: int, c: int| 
                spec_prime(a) && spec_prime(b) && spec_prime(c) && x as int == a * b * c;
            let c1 = choose|a: int, b: int, c: int| 
                spec_prime(a) && spec_prime(b) && spec_prime(c) && x as int == a * b * c;
            assert(spec_prime(a1) && spec_prime(b1) && spec_prime(c1) && x as int == a1 * b1 * c1);
            assert(a1 >= 2 && b1 >= 2 && c1 >= 2);
            assert(a1 * b1 * c1 >= 8);
            assert(x >= 8);
            if a1 < x as int && b1 < x as int && c1 < x as int {
                assert(false);
            } else {
                assert(a1 * b1 * c1 >= x);
                if a1 >= x as int || b1 >= x as int || c1 >= x as int {
                    assert(a1 * b1 * c1 >= 2 * 2 * (x as int));
                    assert(a1 * b1 * c1 >= 4 * (x as int));
                    assert(a1 * b1 * c1 > x as int);
                    assert(false);
                }
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}