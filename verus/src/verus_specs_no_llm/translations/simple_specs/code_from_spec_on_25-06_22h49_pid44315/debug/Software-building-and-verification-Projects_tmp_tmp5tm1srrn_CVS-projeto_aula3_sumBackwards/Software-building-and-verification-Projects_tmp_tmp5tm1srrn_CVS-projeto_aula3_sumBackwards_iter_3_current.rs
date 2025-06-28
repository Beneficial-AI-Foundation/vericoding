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

The invariant works because:
   - Before: `result_old + sum(i_old) == sum(n)`
   - We do: `result_new = result_old + i_old` and `i_new = i_old - 1`
   - After: `result_new + sum(i_new) = (result_old + i_old) + sum(i_old - 1)`
   - Since `sum(i_old) = i_old + sum(i_old - 1)`, we get: `result_old + sum(i_old) = sum(n)` ✓