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

Wait, let me reconsider this. The specification function `Power` is actually correct - it defines `Power(0) = 1` and `Power(n) = 2 * Power(n-1)` for `n > 0`, which gives us `Power(n) = 2^n`.

The issue might be with the loop invariant. Let me trace through:
- Initially: `i = 0`, `result = 1`, and `Power(0) = 1` ✓
- After 1 iteration: `i = 1`, `result = 2`, and `Power(1) = 2 * Power(0) = 2` ✓
- After 2 iterations: `i = 2`, `result = 4`, and `Power(2) = 2 * Power(1) = 4` ✓

The logic looks correct. The issue might be that Verus needs help proving the loop invariant is maintained. Let me add some proof assertions:

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
            proof {
                assert(result == Power(i));
                assert(i + 1 <= N);
            }
            result = result * 2nat;
            i = i + 1;
            proof {
                assert(Power(i) == Power((i - 1) + 1));
                assert(Power(i) == 2nat * Power(i - 1));
            }
        }
        
        result
    }
}

}