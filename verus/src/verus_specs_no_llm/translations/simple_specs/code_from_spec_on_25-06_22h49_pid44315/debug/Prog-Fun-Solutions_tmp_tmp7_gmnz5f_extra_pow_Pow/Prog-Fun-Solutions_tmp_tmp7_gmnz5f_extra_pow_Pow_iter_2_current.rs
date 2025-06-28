use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for exponentiation
spec fn pow(a: nat, n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        a * pow(a, n - 1)
    }
}

fn Pow(a: nat, n: nat) -> (y: nat)
    ensures
        y == pow(a, n)
{
    let mut result: nat = 1;
    let mut i: nat = 0;
    
    while i < n
        invariant
            i <= n,
            result == pow(a, i)
    {
        result = result * a;
        i = i + 1;
    }
    
    result
}

}