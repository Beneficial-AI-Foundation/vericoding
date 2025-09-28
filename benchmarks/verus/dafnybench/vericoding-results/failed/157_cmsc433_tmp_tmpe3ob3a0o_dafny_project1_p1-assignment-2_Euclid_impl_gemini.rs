// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): updated vstd lemma paths for divisibility and div/mod relation */
proof fn lemma_common_divisor_mod(a: int, b: int)
    requires b > 0
    ensures
        forall|d: int| d > 0 ==> ((a % d == 0 && b % d == 0) <==> (b % d == 0 && (a % b) % d == 0)),
{
    assert forall|d: int| d > 0 implies ((a % d == 0 && b % d == 0) <==> (b % d == 0 && (a % b) % d == 0)) by {
        if a % d == 0 && b % d == 0 {
            // d divides a and b, so it must divide r = a - k*b, where r is the remainder.
            vstd::arithmetic::div_mod::lemma_div_mod_relation(a, b);
            vstd::arithmetic::mul::lemma_mul_is_divisible(b, a / b, d);
            vstd::arithmetic::div_mod::lemma_sub_is_divisible(a, (a / b) * b, d);
            assert((a % b) % d == 0);
        }
        if b % d == 0 && (a % b) % d == 0 {
            // d divides b and a % b, so it must divide a = k*b + (a%b).
            vstd::arithmetic::div_mod::lemma_div_mod_relation(a, b);
            vstd::arithmetic::mul::lemma_mul_is_divisible(b, a / b, d);
            vstd::arithmetic::div_mod::lemma_add_is_divisible((a / b) * b, a % b, d);
            assert(a % d == 0);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn euclid(m: int, n: int) -> (gcd: int)
    requires m > 1 && n > 1 && m >= n
    ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): updated vstd lemma paths for divisibility and inequalities */
{
    let mut a = m;
    let mut b = n;

    while b > 0
        invariant
            a > 0,
            b >= 0,
            forall|d: int| d > 0 ==> ((m % d == 0 && n % d == 0) <==> (a % d == 0 && b % d == 0)),
        decreases b
    {
        lemma_common_divisor_mod(a, b);
        let r = a % b;
        a = b;
        b = r;
    }

    // Prove postconditions from loop invariant and termination condition b == 0
    assert(m % a == 0 && n % a == 0) by {
        let inv = |d: int| d > 0 ==> ((m % d == 0 && n % d == 0) <==> (a % d == 0 && b % d == 0));
        assert(inv(a));
        assert(b == 0);
        assert(a % a == 0);
        vstd::arithmetic::div_mod::lemma_mod_of_zero(a);
        assert(b % a == 0);
    };
    
    vstd::arithmetic::div_mod::lemma_div_pos_is_le(m, a);
    vstd::arithmetic::div_mod::lemma_div_pos_is_le(n, a);

    a
}
// </vc-code>

}
fn main() {}