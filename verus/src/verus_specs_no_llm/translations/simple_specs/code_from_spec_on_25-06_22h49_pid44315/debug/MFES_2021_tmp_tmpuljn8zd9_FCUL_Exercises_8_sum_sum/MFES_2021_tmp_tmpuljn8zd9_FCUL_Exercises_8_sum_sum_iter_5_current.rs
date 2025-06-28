The problem is that when `i = n`, we have `i <= n` is true, so we enter the loop body, increment `i` to `n + 1`, but then the decreases expression becomes `n + 1 - (n + 1) = 0`. On the next iteration check, `i <= n` becomes `n + 1 <= n` which is false, so we exit. But Verus needs to verify that the decreases expression is always positive when we enter the loop body.

Let me fix this by adjusting the loop condition:

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn calcSum(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        calcSum(n - 1) + (n - 1)
    }
}

fn sum(n: nat) -> (s: nat)
    ensures
        s == calcSum(n + 1)
{
    let mut i: nat = 0;
    let mut result: nat = 0;
    
    while i < n + 1
        invariant
            i <= n + 1,
            result == calcSum(i),
        decreases n + 1 - i
    {
        result = result + i;
        i = i + 1;
    }
    
    result
}

}

The key changes: