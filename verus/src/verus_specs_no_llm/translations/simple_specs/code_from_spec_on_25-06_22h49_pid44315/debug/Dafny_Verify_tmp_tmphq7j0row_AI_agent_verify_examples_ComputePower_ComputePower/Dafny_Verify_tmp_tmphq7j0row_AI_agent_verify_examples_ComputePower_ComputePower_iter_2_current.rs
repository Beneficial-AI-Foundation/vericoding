use builtin::*;
use builtin_macros::*;

verus! {

spec fn Power(n: int) -> nat
    decreases n
{
    if n <= 0 {
        1nat
    } else {
        (2nat * Power(n - 1)) as nat
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

The key changes I made:


The `decreases n` clause works correctly because:
- When `n <= 0`, we don't make a recursive call
- When `n > 0`, we call `Power(n - 1)` where `n - 1 < n`, ensuring termination

The loop invariant `result == Power(i)` ensures that:
- Initially: `i = 0` and `result = 1nat = Power(0)`
- After each iteration: if `result == Power(i)` before, then `result * 2nat == Power(i + 1)` after
- At termination: `i == N` so `result == Power(N)`