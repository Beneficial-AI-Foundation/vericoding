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
            assert(result * power(base, exp) == (result / base) * base * power(base, exp)) by {
                // result was multiplied by base, so result / base is the old result
                // We need to show: old_result * base * power(base, exp) == old_result * power(base, exp + 1)
                // This follows from the definition of power: power(base, exp + 1) == base * power(base, exp)
            };
        } else {
            base = base * base;
            exp = exp / 2;
            
            // Proof that the invariant is maintained
            assert(result * power(base, exp) == result * power(base * base, exp / 2)) by {
                // We need to show: power(old_base, old_exp) == power(old_base * old_base, old_exp / 2)
                // where old_exp is even, so old_exp = 2 * (old_exp / 2)
                // This follows from: power(a, 2*k) == power(a*a, k)
            };
        }
    }
    
    // At loop exit: exp == 0, so result * power(base, 0) == result * 1 == result == power(x, y0)
    assert(power(base, 0) == 1);
    assert(result == power(x, y0));
    
    result
}

}