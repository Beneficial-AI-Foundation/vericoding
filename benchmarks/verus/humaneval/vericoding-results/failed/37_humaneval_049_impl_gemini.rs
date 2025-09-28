// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * power(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [corrected lemma paths and used correct lemmas] */
proof fn lemma_mod_mul_2(a: int, p: int)
    requires
        p > 0,
    ensures
        ((a % p) * 2) % p == (a * 2) % p,
{
    vstd::arithmetic::div_mod::lemma_mod_auto(a, p);
    vstd::arithmetic::div_mod::lemma_mul_is_congruent(a, a % p, 2, p);
}
// </vc-helpers>

// <vc-spec>
fn modp(n: i8, p: i8) -> (result: i8)
    requires 
        n >= 0 && p > 0,
    ensures 
        result >= 0 && result < p,
        result as int == power(2, n as nat) % (p as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [logic confirmed correct, depends on the fixed helper] */
{
    if p == 1i8 {
        return 0i8;
    }

    let mut result: i8 = 1i8;
    let mut i: i8 = 0i8;

    while i < n
        invariant
            i >= 0 && i <= n,
            result >= 0 && result < p,
            result as int == power(2, i as nat) % (p as int),
        decreases n - i
    {
        proof {
            lemma_mod_mul_2(power(2, i as nat), p as int);
        }

        let temp_res = (result as i16) * 2;
        result = (temp_res % (p as i16)) as i8;
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}