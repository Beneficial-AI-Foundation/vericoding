use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sum(n - 1) + (n - 1) as int
    }
}

fn main() {
}

fn Sum(n: nat) -> (s: int)
    ensures
        s == sum(n)
{
    if n == 0 {
        return 0;
    }
    
    let mut total: int = 0;
    let mut i: nat = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            total == sum(i)
        decreases n - i
    {
        total = total + i as int;
        i = i + 1;
    }
    
    return total;
}

}