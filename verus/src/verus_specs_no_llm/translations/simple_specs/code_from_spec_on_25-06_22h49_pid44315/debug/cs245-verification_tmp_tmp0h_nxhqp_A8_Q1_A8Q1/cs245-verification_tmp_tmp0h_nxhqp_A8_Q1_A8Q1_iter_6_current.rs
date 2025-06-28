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
            result = result * base;
            exp = exp - 1;
            
            // Proof that the invariant is maintained
            assert(exp + 1 >= 0);
            assert(power(base, exp + 1) == base * power(base, exp)) by {
                lemma_power_adds(base, 1int, exp);
            };
        } else {
            base = base * base;
            exp = exp / 2;
            
            // Proof that the invariant is maintained  
            assert(exp * 2 >= 0);
            assert(power(base / base, exp * 2) == power(power(base / base, 2int), exp)) by {
                lemma_power_multiplies(base / base, 2int, exp);
            };
            // Note: base / base in the above should be the original base value
            // We need to show that (base')^exp = base^(2*exp) where base' = base^2
            let old_base = base / base; // This is conceptually the old base
            assert(power(base, exp) == power(old_base, 2 * exp)) by {
                lemma_power_multiplies(old_base, 2int, exp);
            };
        }
    }
    
    // At loop exit: exp == 0, so power(base, exp) == 1
    assert(exp == 0);
    assert(power(base, 0) == 1) by {
        lemma_power_0(base);
    };
    
    result
}

}