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
            assert(result * power(base, exp) == power(x, y0)) by {
                assert(old_exp == exp + 1);
                assert(old_exp % 2 == 1);
                assert(result == old_result * base);
                
                // Use the power lemma: power(base, exp + 1) == base * power(base, exp)
                lemma_power_adds(base, 1, exp);
                assert(power(base, exp + 1) == power(base, 1) * power(base, exp));
                assert(power(base, 1) == base);
                assert(power(base, old_exp) == base * power(base, exp));
                
                // Show the invariant holds
                assert(old_result * power(base, old_exp) == power(x, y0));
                assert(old_result * base * power(base, exp) == power(x, y0));
                assert(result * power(base, exp) == power(x, y0));
            };
        } else {
            let old_base = base;
            let old_exp = exp;
            base = base * base;
            exp = exp / 2;
            
            // Proof that the invariant is maintained
            assert(result * power(base, exp) == power(x, y0)) by {
                assert(old_exp % 2 == 0);
                assert(old_exp == 2 * exp);
                assert(base == old_base * old_base);
                
                // Use the power lemma for even exponents
                lemma_power_multiplies(old_base, 2, exp);
                assert(power(old_base, 2 * exp) == power(power(old_base, 2), exp));
                assert(power(old_base, 2) == old_base * old_base);
                assert(power(old_base, old_exp) == power(old_base * old_base, exp));
                assert(power(old_base, old_exp) == power(base, exp));
                
                // Show the invariant holds
                assert(result * power(old_base, old_exp) == power(x, y0));
                assert(result * power(base, exp) == power(x, y0));
            };
        }
    }
    
    // At loop exit: exp == 0, so result * power(base, 0) == result * 1 == result == power(x, y0)
    lemma_power_0(base);
    assert(power(base, 0) == 1);
    assert(result == power(x, y0));
    
    result
}

}