use builtin::*;
use builtin_macros::*;

verus! {

use vstd::arithmetic::power::*;

fn main() {
}

fn A8Q1(y0: int, x: int) -> (z: int)
    requires
        y0 >= 0
    ensures
        z == power(x, y0)
{
    let mut result: int = 1;
    let mut exp: int = y0;
    let mut base: int = x;
    
    while exp > 0
        invariant
            exp >= 0,
            result * power(base, exp) == power(x, y0)
    {
        if exp % 2 == 1 {
            proof {
                lemma_power_add(base, exp - 1, 1);
                assert(power(base, exp) == power(base, exp - 1 + 1));
                assert(power(base, exp - 1 + 1) == power(base, exp - 1) * power(base, 1));
                lemma_power_1(base);
                assert(power(base, 1) == base);
                assert(power(base, exp) == power(base, exp - 1) * base);
            }
            result = result * base;
            exp = exp - 1;
        } else {
            proof {
                lemma_power_mul(base, 2, exp / 2);
                assert(power(base, exp) == power(base, 2 * (exp / 2)));
                assert(power(base, 2 * (exp / 2)) == power(power(base, 2), exp / 2));
                lemma_power_add(base, 1, 1);
                assert(power(base, 2) == power(base, 1 + 1));
                assert(power(base, 1 + 1) == power(base, 1) * power(base, 1));
                lemma_power_1(base);
                assert(power(base, 1) == base);
                assert(power(base, 2) == base * base);
            }
            base = base * base;
            exp = exp / 2;
        }
    }
    
    proof {
        lemma_power_0(base);
        assert(power(base, 0) == 1);
    }
    
    result
}

}