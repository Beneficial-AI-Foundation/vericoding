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
        return false;
    }
    
    // Try all possible factorizations a * b * c = x where a <= b <= c
    let mut a: u32 = 2;
    while a * a * a <= x
        invariant
            2 <= a,
            forall|a_: int, b_: int, c_: int| 
                2 <= a_ < a && a_ <= b_ <= c_ && spec_prime(a_) && spec_prime(b_) && spec_prime(c_) && x == a_ * b_ * c_ ==> false,
        decreases x - a * a * a,
    {
        if x % a == 0 && is_prime(a) {
            let bc = x / a;
            let mut b: u32 = a;
            while b * b <= bc
                invariant
                    a <= b,
                    bc == x / a,
                    x % a == 0,
                    spec_prime(a as int),
                    forall|b_: int, c_: int|
                        a <= b_ < b && b_ <= c_ && spec_prime(b_) && spec_prime(c_) && bc == b_ * c_ ==> false,
                decreases bc - b * b,
            {
                if bc % b == 0 && is_prime(b) {
                    let c = bc / b;
                    if c >= b && is_prime(c) {
                        assert(x == a * b * c);
                        assert(spec_prime(a as int));
                        assert(spec_prime(b as int));
                        assert(spec_prime(c as int));
                        assert(x as int == (a as int) * (b as int) * (c as int));
                        assert(exists|a_: int, b_: int, c_: int|
                            spec_prime(a_) && spec_prime(b_) && spec_prime(c_) && x == a_ * b_ * c_);
                        return true;
                    }
                }
                b = b + 1;
            }
        }
        a = a + 1;
    }
    
    false
}
// </vc-code>

fn main() {}
}