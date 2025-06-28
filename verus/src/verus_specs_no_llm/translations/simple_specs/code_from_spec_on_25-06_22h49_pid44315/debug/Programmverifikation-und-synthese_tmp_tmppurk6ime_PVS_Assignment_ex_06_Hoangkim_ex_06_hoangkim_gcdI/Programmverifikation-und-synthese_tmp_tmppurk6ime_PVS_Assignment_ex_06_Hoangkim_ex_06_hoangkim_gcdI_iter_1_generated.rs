use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn gcdI(m: int, n: int) -> (d: int)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m, n)
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
        let temp = a % b;
        a = b;
        b = temp;
    }
    
    a
}

}