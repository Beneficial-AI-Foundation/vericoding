use builtin::*;
use builtin_macros::*;

verus! {

// Specification function to define what Power means
spec fn Power(n: int) -> nat
    decreases n
{
    if n <= 0 {
        1nat
    } else {
        2nat * Power(n - 1)
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
        1nat
    } else {
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
        
        result
    }
}

}