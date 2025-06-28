use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to define the sum of integers from 0 to n
spec fn sumInts(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        n + sumInts(n - 1)
    }
}

fn main() {
}

fn SumIntsLoop(n: int) -> (s: int)
    requires
        n >= 0
    ensures
        s == sumInts(n),
        s == n*(n+1)/2
{
    let mut sum = 0;
    let mut i = 0;
    
    while i <= n
        invariant
            0 <= i <= n + 1,
            sum == sumInts(i - 1),
            sum == (i - 1) * i / 2
    {
        sum = sum + i;
        i = i + 1;
    }
    
    sum
}

}