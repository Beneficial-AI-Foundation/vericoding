// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
{/* helper modified by LLM (iteration 5): safe u32 primality test using division to avoid overflow */
fn is_prime_u32(p: u32) -> bool {
    if p <= 1u32 {
        false
    } else {
        let p64: u64 = p as u64;
        let mut i: u64 = 2u64;
        while i <= p64 / i
            invariant
                2u64 <= i,
                i <= p64,
            decreases
                p64 + 1u64 - i
        {
            if p64 % i == 0u64 {
                return false;
            }
            i = i + 1u64;
        }
        true
    }
}}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)

    requires
        x > 1,

    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): search for three prime factors using u64 for safe arithmetic and assertions to establish loop invariants */
    let n: u32 = x;
    let n64: u64 = n as u64;
    let mut a: u32 = 2u32;
    while (a as u64) <= n64
        invariant
            2u32 <= a,
            (a as u64) <= n64 + 1u64,
        decreases
            n64 + 1u64 - (a as u64)
    {
        if n % a == 0u32 {
            if is_prime_u32(a) {
                let m: u32 = n / a;
                // m >= 1 because a divides n and a <= n
                assert(m >= 1u32);
                let m64: u64 = m as u64;
                let mut b: u32 = 2u32;
                // establish invariant precondition for b-loop
                assert((b as u64) <= m64 + 1u64);
                while (b as u64) <= m64
                    invariant
                        2u32 <= b,
                        (b as u64) <= m64 + 1u64,
                    decreases
                        m64 + 1u64 - (b as u64)
                {
                    if m % b == 0u32 {
                        if is_prime_u32(b) {
                            let c: u32 = m / b;
                            if c > 1u32 && is_prime_u32(c) {
                                return true;
                            }
                        }
                    }
                    b = b + 1u32;
                }
            }
        }
        a = a + 1u32;
    }
    false
}
// </vc-code>

}
fn main() {}