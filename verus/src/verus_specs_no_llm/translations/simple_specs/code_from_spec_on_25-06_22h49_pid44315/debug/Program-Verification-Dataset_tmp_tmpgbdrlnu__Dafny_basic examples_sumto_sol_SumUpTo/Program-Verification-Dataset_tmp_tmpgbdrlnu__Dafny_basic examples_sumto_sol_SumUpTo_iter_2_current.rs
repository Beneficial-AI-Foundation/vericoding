use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum_up_to(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        (n - 1) + sum_up_to(n - 1)
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

Wait, I need to reconsider this. The spec function as written computes `(n-1) + sum_up_to(n-1)`, but what we want is the sum `0 + 1 + ... + (n-1)`. Let me fix the spec function:

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

This should now correctly verify because:
- `sum_up_to(0) = 0`
- `sum_up_to(1) = sum_up_to(0) + 0 = 0`
- `sum_up_to(2) = sum_up_to(1) + 1 = 1`
- `sum_up_to(3) = sum_up_to(2) + 2 = 3`
- And so on...

The loop invariant `sum == sum_up_to(i)` should hold throughout the execution, and when the loop exits with `i == n`, we have `sum == sum_up_to(n)`.