use builtin::*;
use builtin_macros::*;

verus! {

spec fn Power(n: int) -> nat
    decreases n when n >= 0
{
    if n <= 0 {
        1nat
    } else {
        2nat * Power((n - 1) as nat)
    }
}

fn main() {
}

fn ComputePower(N: int) -> (y: nat)
    requires
        N >= 0
    ensures
        y == Power(N)
{
    if N == 0 {
        return 1nat;
    }
    
    let mut result: nat = 1nat;
    let mut i: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            result == Power(i)
        decreases N - i
    {
        result = result * 2nat;
        i = i + 1;
    }
    
    return result;
}

}