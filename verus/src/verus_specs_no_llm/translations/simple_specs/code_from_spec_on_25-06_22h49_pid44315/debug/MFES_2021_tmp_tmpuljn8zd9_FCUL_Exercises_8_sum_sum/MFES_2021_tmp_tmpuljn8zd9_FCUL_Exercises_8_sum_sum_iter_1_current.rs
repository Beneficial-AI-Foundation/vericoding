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
        (n - 1) + calcSum(n - 1)
    }
}

fn sum(n: nat) -> (s: nat)
    ensures
        s == calcSum(n + 1)
{
    let mut i: nat = 0;
    let mut result: nat = 0;
    
    while i <= n
        invariant
            i <= n + 1,
            result == calcSum(i)
        decreases n + 1 - i
    {
        result = result + i;
        i = i + 1;
    }
    
    result
}

}