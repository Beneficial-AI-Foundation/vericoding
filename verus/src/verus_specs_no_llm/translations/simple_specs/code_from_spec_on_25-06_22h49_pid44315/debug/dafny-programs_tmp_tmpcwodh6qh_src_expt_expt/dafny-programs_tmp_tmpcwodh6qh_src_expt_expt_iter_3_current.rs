use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for exponentiation
spec fn Expt(b: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        1
    } else {
        b * Expt(b, (n - 1) as nat)
    }
}

fn expt(b: int, n: nat) -> (res: int)
    ensures
        res == Expt(b, n)
{
    let mut result = 1;
    let mut i: nat = 0;
    
    while i < n
        invariant
            i <= n,
            result == Expt(b, i),
    {
        result = result * b;
        i = i + 1;
    }
    
    result
}

}