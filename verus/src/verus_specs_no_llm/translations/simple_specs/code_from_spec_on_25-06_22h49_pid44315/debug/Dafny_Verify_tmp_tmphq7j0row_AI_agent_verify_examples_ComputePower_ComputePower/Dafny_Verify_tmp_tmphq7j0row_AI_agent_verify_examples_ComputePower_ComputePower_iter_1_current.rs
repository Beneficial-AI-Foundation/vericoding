use builtin::*;
use builtin_macros::*;

verus! {

spec fn Power(n: int) -> nat
    decreases n
{
    if n <= 0 {
        1
    } else {
        2 * Power(n - 1)
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
        return 1;
    }
    
    let mut result: nat = 1;
    let mut i: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            result == Power(i)
        decreases N - i
    {
        result = result * 2;
        i = i + 1;
    }
    
    return result;
}

}

The implementation:


   - Handles the base case N = 0 by returning 1
   - Uses a loop to iteratively compute 2^N by multiplying by 2, N times
   - The loop invariant ensures that at each step, `result` equals `Power(i)`
   - When the loop terminates (i = N), we have `result == Power(N)`

The function preserves all the original constraints:
- `requires N >= 0` 
- `ensures y == Power(N)`

The loop invariant and decreases clause ensure the verification succeeds by proving that the iterative computation correctly matches the recursive specification.