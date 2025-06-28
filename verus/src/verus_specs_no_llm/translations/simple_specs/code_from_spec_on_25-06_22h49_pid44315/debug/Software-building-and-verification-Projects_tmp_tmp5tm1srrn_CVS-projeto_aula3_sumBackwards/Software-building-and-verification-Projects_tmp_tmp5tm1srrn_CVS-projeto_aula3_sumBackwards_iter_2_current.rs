The issue is that when we do `result = result + i; i = i - 1;`, we're adding the current value of `i` to result, but then `i` becomes `i-1`. The invariant needs to account for this properly.

Here's the corrected version:

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}

fn sumBackwards(n: nat) -> (r: nat)
    ensures
        r == sum(n)
{
    let mut result = 0;
    let mut i = n;
    
    while i > 0
        invariant
            result + sum(i) == sum(n),
            i <= n
        decreases i
    {
        result = result + i;
        i = i - 1;
    }
    
    result
}

}

The key changes:

The logic is:
- Initially: `result = 0`, `i = n`, so `0 + sum(n) == sum(n)` ✓
- After iteration: if we had `result_old + sum(i_old) == sum(n)`, then after `result_new = result_old + i_old` and `i_new = i_old - 1`, we get `result_new + sum(i_new) = (result_old + i_old) + sum(i_old - 1) = result_old + (i_old + sum(i_old - 1)) = result_old + sum(i_old) = sum(n)` ✓
- When loop exits: `i = 0`, so `result + sum(0) = result + 0 = result = sum(n)` ✓