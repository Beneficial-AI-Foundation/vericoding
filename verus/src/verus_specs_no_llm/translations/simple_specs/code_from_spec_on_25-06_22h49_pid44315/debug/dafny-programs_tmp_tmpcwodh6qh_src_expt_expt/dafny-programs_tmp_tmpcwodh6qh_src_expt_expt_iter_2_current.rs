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
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result == Expt(b, i),
    {
        result = result * b;
        i = i + 1;
    }
    
    result
}

}

The key changes I made:




The implementation uses an iterative approach with loop invariants:
- `0 <= i <= n`: bounds check for the counter
- `result == Expt(b, i)`: maintains correctness - the result always equals b^i

This allows Verus to verify that when the loop terminates (i == n), we have `result == Expt(b, n)`, which satisfies the postcondition.