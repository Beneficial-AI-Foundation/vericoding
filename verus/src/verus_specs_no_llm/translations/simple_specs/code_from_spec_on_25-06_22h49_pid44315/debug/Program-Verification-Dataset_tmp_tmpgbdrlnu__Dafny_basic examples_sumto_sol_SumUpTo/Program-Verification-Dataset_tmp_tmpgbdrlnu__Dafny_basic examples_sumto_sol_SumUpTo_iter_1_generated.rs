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