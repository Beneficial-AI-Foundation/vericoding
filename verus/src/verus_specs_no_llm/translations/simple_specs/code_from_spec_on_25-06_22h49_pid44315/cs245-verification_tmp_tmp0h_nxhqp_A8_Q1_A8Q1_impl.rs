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
                // We know exp > 0 and exp % 2 == 1, so exp >= 1
                assert(exp >= 1);
                // Use the fact that power(base, exp) = base * power(base, exp-1)
                lemma_power_add_one_auto();
                assert(power(base, exp) == base * power(base, exp - 1));
                // Therefore: result * power(base, exp) = result * base * power(base, exp - 1)
                assert(result * power(base, exp) == result * base * power(base, exp - 1));
                // This equals power(x, y0), so after update: (result * base) * power(base, exp - 1) == power(x, y0)
            }
            result = result * base;
            exp = exp - 1;
        } else {
            proof {
                // We know exp > 0 and exp % 2 == 0, so exp >= 2
                assert(exp >= 2);
                assert(exp % 2 == 0);
                // Use the property that power(base, exp) = power(base*base, exp/2) when exp is even
                lemma_power_mul_auto();
                assert(exp == 2 * (exp / 2));
                assert(power(base, exp) == power(base, 2 * (exp / 2)));
                assert(power(base, 2 * (exp / 2)) == power(power(base, 2), exp / 2));
                
                // Show that power(base, 2) == base * base
                lemma_power_adds(base, 1, 1);
                assert(power(base, 2) == power(base, 1 + 1));
                assert(power(base, 1 + 1) == power(base, 1) * power(base, 1));
                lemma_power_1(base);
                assert(power(base, 1) == base);
                assert(power(base, 2) == base * base);
                
                // Therefore power(base, exp) = power(base * base, exp / 2)
                assert(power(base, exp) == power(base * base, exp / 2));
                // So result * power(base, exp) = result * power(base * base, exp / 2)
                assert(result * power(base, exp) == result * power(base * base, exp / 2));
            }
            base = base * base;
            exp = exp / 2;
        }
    }
    
    proof {
        // When exp == 0, power(base, 0) == 1
        assert(exp == 0);
        lemma_power_0(base);
        assert(power(base, 0) == 1);
        assert(result * power(base, exp) == result * 1);
        assert(result * 1 == result);
        assert(result == power(x, y0));
    }
    
    result
}

}