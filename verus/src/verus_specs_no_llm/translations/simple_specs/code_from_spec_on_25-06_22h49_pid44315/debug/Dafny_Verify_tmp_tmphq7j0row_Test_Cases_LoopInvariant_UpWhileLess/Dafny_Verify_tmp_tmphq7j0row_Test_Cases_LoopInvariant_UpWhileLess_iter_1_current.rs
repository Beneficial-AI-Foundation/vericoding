// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn UpWhileLess(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == N
{
    let mut i: int = 0;
    
    while i < N
        invariant 0 <= i <= N
    {
        i = i + 1;
    }
    
    return i;
}

}