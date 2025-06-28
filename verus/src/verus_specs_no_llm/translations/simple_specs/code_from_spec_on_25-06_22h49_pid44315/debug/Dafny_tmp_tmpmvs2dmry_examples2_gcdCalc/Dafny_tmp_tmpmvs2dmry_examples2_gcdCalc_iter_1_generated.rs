use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn gcdCalc(m: nat, n: nat) -> (res: nat)
    requires
        m > 0 && n > 0
    ensures
        res == gcd(m, n)
{
    let mut a = m;
    let mut b = n;
    
    while b > 0
        invariant
            a > 0,
            gcd(a, b) == gcd(m, n)
    {
        let temp = b;
        b = a % b;
        a = temp;
    }
    
    a
}

}