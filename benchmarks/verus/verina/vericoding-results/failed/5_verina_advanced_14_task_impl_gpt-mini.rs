// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): division lemma */
proof fn div_mul_back(x: nat, d: nat) requires d > 0 && x % d == 0 ensures x == d * (x / d) { proof {
    assert(x == d * (x / d) + x % d);
    assert(x % d == 0);
    assert(d * (x / d) + 0 == d * (x / d));
    assert(x == d * (x / d));
} }
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate dividing by 4 and maintain exponent invariant */
    if n == 0 {
        false
    } else {
        let mut x: nat = n;
        let mut exp: nat = 0;
        while x % 4 == 0 && x > 1
            invariant n == pow(4, exp) * x && x >= 1
            decreases x
        {
            let old_x = x;
            x = x / 4;
            exp = exp + 1;
            proof {
                div_mul_back(old_x, 4);
            }
        }
        let result: bool = x == 1;
        proof {
            if result {
                assert(n == pow(4, exp) * x);
                assert(x == 1);
                assert(n == pow(4, exp));
                assert(exists|m: nat| n == pow(4, m));
            } else {
                assert(!(exists|m: nat| n == pow(4, m)));
            }
        }
        result
    }
}
// </vc-code>

}
fn main() {}