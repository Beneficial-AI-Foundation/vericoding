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
        // Add proof assertion to help verification
        assert(sum(i) == i + sum(i - 1));
        result = result + i;
        i = i - 1;
    }
    
    // At loop exit: i == 0, so sum(i) == sum(0) == 0
    // Therefore: result + 0 == sum(n), which means result == sum(n)
    assert(i == 0);
    assert(sum(0) == 0);
    assert(result + sum(i) == sum(n));
    assert(result == sum(n));
    
    result
}

}