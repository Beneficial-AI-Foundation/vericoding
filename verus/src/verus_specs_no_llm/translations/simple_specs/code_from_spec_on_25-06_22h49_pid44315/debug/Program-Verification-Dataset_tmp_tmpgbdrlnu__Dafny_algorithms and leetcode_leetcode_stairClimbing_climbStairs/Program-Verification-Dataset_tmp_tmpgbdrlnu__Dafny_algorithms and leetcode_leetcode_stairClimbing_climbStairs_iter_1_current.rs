use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fibonacci(n: nat) -> nat
    decreases n
{
    if n <= 1 {
        1
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

fn climbStairs(n: nat) -> (count: nat)
    ensures
        count > 0,
        count == fibonacci(n)
{
    if n == 0 {
        1
    } else if n == 1 {
        1
    } else {
        let mut prev2 = 1;
        let mut prev1 = 1;
        let mut i = 2;
        
        while i <= n
            invariant
                i >= 2,
                i <= n + 1,
                prev2 == fibonacci((i - 2) as nat),
                prev1 == fibonacci((i - 1) as nat)
        {
            let current = prev1 + prev2;
            prev2 = prev1;
            prev1 = current;
            i = i + 1;
        }
        
        prev1
    }
}

}