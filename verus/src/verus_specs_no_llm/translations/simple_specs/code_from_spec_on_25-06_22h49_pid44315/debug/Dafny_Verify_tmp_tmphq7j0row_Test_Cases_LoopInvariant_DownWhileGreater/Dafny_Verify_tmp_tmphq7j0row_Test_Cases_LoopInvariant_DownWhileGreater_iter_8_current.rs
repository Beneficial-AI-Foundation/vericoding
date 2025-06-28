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
            0 <= current <= N,
            current >= 0
        decreases current
    {
        current = current - 1;
    }
    assert(current >= 0);  // From invariant
    assert(!(current > 0)); // Loop condition is false
    assert(current == 0);   // Therefore current must be 0
    current
}

}