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
        invariant 0 <= current <= N
        decreases current
    {
        current = current - 1;
    }
    current
}

}