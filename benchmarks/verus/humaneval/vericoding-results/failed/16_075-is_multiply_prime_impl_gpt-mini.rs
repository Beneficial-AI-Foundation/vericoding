// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): deterministic u32 primality test */
fn is_prime_dec(p: u32) -> bool
    requires
        p > 1,
{
    let mut i: u32 = 2;
    while i < p
        invariant
            2 <= i && i <= p,
        decreases p - i
    {
        if p % i == 0 {
            return false;
        }
        i = i + 1;
    }
    true
}

/* helper modified by LLM (iteration 5): correctness lemma linking is_prime_dec and spec_prime */
proof fn is_prime_dec_equiv(p: u32)
    requires
        p > 1,
    ensures
        is_prime_dec(p) == spec_prime(p as int),
{
    proof {
        if is_prime_dec(p) {
            assert(forall|k: int| 1 < k < p as int ==> (p as int) % k != 0);
        }
        if spec_prime(p as int) {
            assert(is_prime_dec(p));
        }
    }
}
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
    /* code modified by LLM (iteration 5): search for three prime factors using u32 arithmetic */
    let x_u: u32 = x;
    let mut a: u32 = 2;
    while a <= x_u
        invariant
            2 <= a && a <= x_u + 1,
        decreases x_u - a + 1
    {
        if is_prime_dec(a) {
            let mut b: u32 = 2;
            while b <= x_u
                invariant
                    2 <= b && b <= x_u + 1,
                decreases x_u - b + 1
            {
                if is_prime_dec(b) {
                    let prod: u32 = a * b;
                    if prod != 0 && prod <= x_u {
                        if x_u % prod == 0 {
                            let c: u32 = x_u / prod;
                            if c > 1 && is_prime_dec(c) {
                                return true;
                            }
                        }
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

}
fn main() {}