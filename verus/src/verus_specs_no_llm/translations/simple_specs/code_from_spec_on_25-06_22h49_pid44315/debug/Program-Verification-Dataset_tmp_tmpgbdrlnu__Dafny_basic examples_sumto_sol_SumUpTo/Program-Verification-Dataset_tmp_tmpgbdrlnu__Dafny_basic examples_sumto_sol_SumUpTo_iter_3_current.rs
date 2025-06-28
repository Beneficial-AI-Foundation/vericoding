use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum_up_to(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        sum_up_to(n - 1) + (n - 1)
    }
}

fn SumUpTo(n: nat) -> (r: nat)
    ensures
        r == sum_up_to(n)
{
    let mut i: nat = 0;
    let mut sum: nat = 0;
    
    while i < n
        invariant
            i <= n,
            sum == sum_up_to(i)
        decreases n - i
    {
        sum = sum + i;
        i = i + 1;
    }
    
    sum
}

fn main() {
}

}

The key change is in the spec function: `sum_up_to(n - 1) + (n - 1)` instead of `(n - 1) + sum_up_to(n - 1)`. This ensures that:
- `sum_up_to(n)` = sum of integers from 0 to n-1
- The loop invariant `sum == sum_up_to(i)` holds because at each iteration, `sum` contains the sum of integers from 0 to i-1
- When the loop exits with `i == n`, we have `sum == sum_up_to(n)`

This should now verify correctly.