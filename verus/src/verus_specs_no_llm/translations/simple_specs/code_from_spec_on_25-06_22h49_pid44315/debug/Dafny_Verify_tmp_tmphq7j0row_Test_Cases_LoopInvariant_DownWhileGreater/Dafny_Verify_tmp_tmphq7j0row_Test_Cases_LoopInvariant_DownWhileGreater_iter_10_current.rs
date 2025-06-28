use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DownWhileGreater(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == 0
{
    let mut current = N;
    while current > 0
        invariant 
            0 <= current <= N
        decreases current
    {
        current = current - 1;
    }
    
    // After the loop, we know:
    // 1. The invariant holds: 0 <= current <= N
    // 2. The loop condition is false: !(current > 0), which means current <= 0
    // 3. Combining these: current <= 0 && 0 <= current, so current == 0
    
    assert(0 <= current);    // From invariant
    assert(current <= 0);    // From negated loop condition
    
    current
}

}