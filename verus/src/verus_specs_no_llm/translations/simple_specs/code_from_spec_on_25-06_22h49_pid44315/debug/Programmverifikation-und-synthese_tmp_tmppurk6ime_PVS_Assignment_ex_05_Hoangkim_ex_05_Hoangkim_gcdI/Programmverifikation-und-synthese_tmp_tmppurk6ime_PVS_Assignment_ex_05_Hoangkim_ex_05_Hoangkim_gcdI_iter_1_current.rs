use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn gcdI(m: int, n: int) -> (g: int)
    requires
        m > 0 && n > 0
    ensures
        g == gcd(m, n)
{
    let mut a = m;
    let mut b = n;
    
    while b != 0
        invariant
            gcd(a, b) == gcd(m, n),
            a > 0,
            b >= 0
        decreases b
    {
        let temp = b;
        b = a % b;
        a = temp;
    }
    
    a
}

}

The implementation uses the Euclidean algorithm:

   - Store `b` in a temporary variable
   - Set `b = a % b` 
   - Set `a = temp`

The loop invariants ensure:
- `gcd(a, b) == gcd(m, n)` - the GCD of the current values equals the GCD of the original inputs
- `a > 0` - `a` remains positive throughout
- `b >= 0` - `b` is non-negative

The `decreases b` clause proves termination since `b` strictly decreases in each iteration (due to the modulo operation) and remains non-negative.