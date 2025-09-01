use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
spec fn is_prime(n: u32) -> bool {
    n > 1 && forall|k: u32| 1 < k < n ==> #[trigger] (n % k) != 0
}

proof fn prime_lemma(p: u32)
    requires
        is_prime(p),
    ensures
        spec_prime(p as int)
{
    assert(forall|k: int| 1 < k < (p as int) ==> {
        (k >= 2 && k <= (p as int - 1)) && (p % (k as u32) != 0)
    });
}

proof fn prime_lemma_reverse(p: u32)
    requires
        spec_prime(p as int),
    ensures
        is_prime(p)
{
    assert(forall|k: u32| 1 < k < p ==> {
        (k as int > 1 && k as int < (p as int)) && ((p as int) % (k as int) != 0)
    });
}

proof fn mult_prime_implies_exists(a: u32, b: u32, c: u32, x: u32)
    requires
        is_prime(a) && is_prime(b) && is_prime(c),
        x == a * b * c,
    ensures
        exists|a': int, b': int, c': int|
            spec_prime(a') && spec_prime(b') && spec_prime(c') && x as int == a' * b' * c'
{
    prime_lemma(a);
    prime_lemma(b);
    prime_lemma(c);
    assert(spec_prime(a as int) && spec_prime(b as int) && spec_prime(c as int));
    assert((a * b * c) as int == (a as int) * (b as int) * (c as int));
}

proof fn exists_implies_mult_prime(a: int, b: int, c: int, x: u32)
    requires
        spec_prime(a) && spec_prime(b) && spec_prime(c),
        x as int == a * b * c,
    ensures
        exists|a': u32, b': u32, c': u32|
            is_prime(a') && is_prime(b') && is_prime(c') && x == a' * b' * c'
{
    assert(a > 1 && b > 1 && c > 1);
    assert(a < 0x80000000 && b < 0x80000000 && c < 0x80000000);
    
    let a_u32 = a as u32;
    let b_u32 = b as u32;
    let c_u32 = c as u32;
    
    prime_lemma_reverse(a_u32);
    prime_lemma_reverse(b_u32);
    prime_lemma_reverse(c_u32);
    assert(is_prime(a_u32) && is_prime(b_u32) && is_prime(c_u32));
    assert(x == a_u32 * b_u32 * c_u32);
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
    let mut i = 2;
    while i < x
        invariant
            2 <= i <= x,
            forall|a: u32, b: u32, c: u32| 
                2 <= a < i && is_prime(a) && is_prime(b) && is_prime(c) && x == a * b * c ==> #[trigger] false,
    {
        if x % i == 0 {
            let factor1 = i;
            let remaining = x / i;
            let mut j = 2;
            
            while j < remaining
                invariant
                    2 <= j <= remaining,
                    forall|b: u32, c: u32| 
                        2 <= b < j && is_prime(b) && is_prime(c) && remaining == b * c ==> #[trigger] false,
            {
                if remaining % j == 0 {
                    let factor2 = j;
                    let factor3 = remaining / j;
                    
                    if is_prime(factor1) && is_prime(factor2) && is_prime(factor3) {
                        assert(is_prime(factor1));
                        assert(is_prime(factor2));
                        assert(is_prime(factor3));
                        assert(x == factor1 * factor2 * factor3);
                        mult_prime_implies_exists(factor1, factor2, factor3, x);
                        return true;
                    }
                }
                j += 1;
            }
            
            if is_prime(factor1) && is_prime(remaining) {
                proof {
                    let factor3 = 1u32;
                    // But 1 is not prime, so this doesn't give us three primes
                }
            }
        }
        i += 1;
    }
    
    proof {
        assert forall|a: int, b: int, c: int| spec_prime(a) && spec_prime(b) && spec_prime(c) implies x as int != a * b * c by {
            if x as int == a * b * c {
                exists_implies_mult_prime(a, b, c, x);
                assert(false); // Contradiction since we didn't find the factors
            }
        }
    }
    
    false
}
// </vc-code>

fn main() {}
}