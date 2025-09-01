use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn is_prime(p: u32) -> (ret: bool)
    ensures
        ret <==> spec_prime(p as int),
{
    if p <= 1 {
        return false;
    }
    
    let mut k: u32 = 2;
    while k < p
        invariant
            2 <= k <= p,
            forall|j: int| 1 < j < k ==> #[trigger] ((p as int) % j) != 0,
        decreases p - k,
    {
        if p % k == 0 {
            assert((p as int) % (k as int) == 0);
            return false;
        }
        k = k + 1;
    }
    
    assert(forall|j: int| 1 < j < p ==> #[trigger] ((p as int) % j) != 0);
    true
}

proof fn no_three_primes_product_below_8()
    ensures
        forall|x: int| 1 < x <= 7 ==> 
            !exists|a: int, b: int, c: int| 
                spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
{
    // The smallest product of three primes is 2*2*2 = 8
    assert(spec_prime(2));
    assert(forall|p: int| spec_prime(p) ==> p >= 2);
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
    if x <= 7 {
        // Smallest product of three primes is 2*2*2 = 8
        proof {
            no_three_primes_product_below_8();
        }
        return false;
    }
    
    // Try all possible factorizations a * b * c = x where a <= b <= c
    let mut a: u32 = 2;
    while a <= x && a as int * a as int * a as int <= x as int
        invariant
            2 <= a,
            a <= x + 1,
            forall|a_: int, b_: int, c_: int| 
                2 <= a_ < a && a_ <= b_ <= c_ && spec_prime(a_) && spec_prime(b_) && spec_prime(c_) && x as int == a_ * b_ * c_ ==> false,
        decreases x + 1 - a,
    {
        if a as int * a as int * a as int > x as int {
            break;
        }
        
        if x % a == 0 && is_prime(a) {
            let bc = x / a;
            let mut b: u32 = a;
            while b <= bc && b as int * b as int <= bc as int
                invariant
                    a <= b,
                    b <= bc + 1,
                    bc == x / a,
                    x % a == 0,
                    spec_prime(a as int),
                    x as int == a as int * bc as int,
                    forall|b_: int, c_: int|
                        a as int <= b_ < b as int && b_ <= c_ && spec_prime(b_) && spec_prime(c_) && bc as int == b_ * c_ ==> false,
                decreases bc + 1 - b,
            {
                if b as int * b as int > bc as int {
                    break;
                }
                
                if bc % b == 0 && is_prime(b) {
                    let c = bc / b;
                    if c >= b && is_prime(c) {
                        assert(bc as int == b as int * c as int);
                        assert(x as int == a as int * bc as int);
                        assert(x as int == a as int * (b as int * c as int));
                        assert(x as int == (a as int) * (b as int) * (c as int)) by {
                            assert(a as int * (b as int * c as int) == (a as int * b as int) * c as int);
                        }
                        assert(spec_prime(a as int));
                        assert(spec_prime(b as int));
                        assert(spec_prime(c as int));
                        return true;
                    }
                }
                if b < bc {
                    b = b + 1;
                } else {
                    break;
                }
            }
        }
        if a < x {
            a = a + 1;
        } else {
            break;
        }
    }
    
    assert(forall|a_: int, b_: int, c_: int| 
        2 <= a_ && a_ <= b_ <= c_ && a_ * a_ * a_ <= x as int && spec_prime(a_) && spec_prime(b_) && spec_prime(c_) && x as int == a_ * b_ * c_ ==> false);
    false
}
// </vc-code>

fn main() {}
}