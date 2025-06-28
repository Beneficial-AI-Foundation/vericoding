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
            proof {
                lemma_power_positive(base, exp);
                lemma_power_adds(base, 1int, exp);
            }
        } else {
            base = base * base;
            exp = exp / 2;
            
            // Proof that the invariant is maintained  
            proof {
                lemma_power_positive(base, exp);
                lemma_power_multiplies(x, 2int, exp);
            }
        }
    }
    
    // At loop exit: exp == 0
    proof {
        lemma_power_0(base);
    }
    
    result
}

}