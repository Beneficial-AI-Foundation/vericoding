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
            let old_result = result;
            let old_exp = exp;
            result = result * base;
            exp = exp - 1;
            
            // Proof that the invariant is maintained
            assert(old_result * power(base, old_exp) == power(x, y0));
            assert(old_exp == exp + 1);
            assert(power(base, old_exp) == power(base, exp + 1));
            assert(power(base, exp + 1) == base * power(base, exp)) by {
                lemma_power_add_one_auto();
            }
            assert(old_result * power(base, old_exp) == old_result * base * power(base, exp));
            assert(result == old_result * base);
            assert(result * power(base, exp) == power(x, y0));
        } else {
            let old_base = base;
            let old_exp = exp;
            base = base * base;
            exp = exp / 2;
            
            // Proof that the invariant is maintained
            assert(result * power(old_base, old_exp) == power(x, y0));
            assert(old_exp == 2 * exp);
            assert(power(old_base, old_exp) == power(old_base, 2 * exp));
            assert(power(old_base, 2 * exp) == power(power(old_base, 2), exp)) by {
                lemma_power_mul_auto();
            }
            assert(power(old_base, 2) == old_base * old_base) by {
                lemma_power_add_one_auto();
                lemma_power_add_one_auto();
                assert(power(old_base, 2) == power(old_base, 1 + 1));
                assert(power(old_base, 1 + 1) == old_base * power(old_base, 1));
                assert(power(old_base, 1) == old_base) by {
                    lemma_power_one_auto();
                }
            }
            assert(base == old_base * old_base);
            assert(power(old_base, 2) == base);
            assert(power(power(old_base, 2), exp) == power(base, exp));
            assert(result * power(base, exp) == power(x, y0));
        }
    }
    
    // At loop exit: exp == 0, so power(base, exp) == 1
    assert(exp == 0);
    assert(power(base, 0) == 1) by {
        lemma_power_0_auto();
    }
    assert(result * 1 == power(x, y0));
    assert(result == power(x, y0));
    
    result
}

}