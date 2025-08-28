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
        ret.is_none() ==> (x as int) * (y as int) * (z as int) > u32::MAX as int,
{
    if (x == 0 || y == 0 || z == 0) {
        return Some(0);
    }
    
    let prod2 = x.checked_mul(y);
    if prod2.is_some() {
        let prod3 = prod2.unwrap().checked_mul(z);
        if prod3.is_some() {
            let ans = prod3.unwrap();
            proof {
                assert(prod2.unwrap() == x * y);
                assert(ans == prod2.unwrap() * z);
                assert(ans == x * y * z);
            }
            Some(ans)
        } else {
            proof {
                assert(prod2.unwrap() == x * y);
                assert(prod2.unwrap().checked_mul(z).is_none());
                assert((prod2.unwrap() as int) * (z as int) > u32::MAX as int);
                assert((x as int) * (y as int) * (z as int) > u32::MAX as int);
            }
            None
        }
    } else {
        proof {
            assert(x.checked_mul(y).is_none());
            assert((x as int) * (y as int) > u32::MAX as int);
            assert((x as int) * (y as int) * (z as int) > u32::MAX as int);
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
            forall|a_val: int, b_val: int, c_val: int|
                2 <= a_val < a && 2 <= b_val < x && 2 <= c_val < x &&
                spec_prime(a_val) && spec_prime(b_val) && spec_prime(c_val) &&
                a_val * b_val * c_val <= u32::MAX as int ==> a_val * b_val * c_val != x,
            a <= x,
    {
        if prime(a) {
            for b in 2..x
                invariant
                    forall|b_val: int, c_val: int|
                        2 <= b_val < b && 2 <= c_val < x &&
                        spec_prime(b_val) && spec_prime(c_val) &&
                        (a as int) * b_val * c_val <= u32::MAX as int ==> (a as int) * b_val * c_val != x,
                    b <= x,
                    spec_prime(a as int),
            {
                if prime(b) {
                    for c in 2..x
                        invariant
                            forall|c_val: int|
                                2 <= c_val < c &&
                                spec_prime(c_val) &&
                                (a as int) * (b as int) * c_val <= u32::MAX as int ==> (a as int) * (b as int) * c_val != x,
                            c <= x,
                            spec_prime(a as int),
                            spec_prime(b as int),
                    {
                        if prime(c) {
                            let product = checked_mul_thrice(a, b, c);
                            if product.is_some() && product.unwrap() == x {
                                assert(spec_prime(a as int) && spec_prime(b as int) && spec_prime(c as int));
                                assert(x == (a as int) * (b as int) * (c as int));
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    
    proof {
        if exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c {
            let a_witness = choose|a: int| #[trigger] exists|b: int, c: int|
                spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c;
            let b_witness = choose|b: int| #[trigger] exists|c: int|
                spec_prime(a_witness) && spec_prime(b) && spec_prime(c) && x == a_witness * b * c;
            let c_witness = choose|c: int| #[trigger] 
                spec_prime(a_witness) && spec_prime(b_witness) && spec_prime(c) && x == a_witness * b_witness * c;
            
            assert(spec_prime(a_witness) && spec_prime(b_witness) && spec_prime(c_witness));
            assert(x == a_witness * b_witness * c_witness);
            assert(a_witness > 1 && b_witness > 1 && c_witness > 1);
            assert(a_witness * b_witness * c_witness >= 8);
            assert(2 <= a_witness < x && 2 <= b_witness < x && 2 <= c_witness < x);
            assert(a_witness * b_witness * c_witness <= u32::MAX as int);
            assert(false);
        }
    }
    
    false
}
// </vc-code>

}
fn main() {}