use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn UpWhileNotEqual(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == N
{
    let mut i: int = 0;
    
    while i != N
        invariant
            0 <= i <= N
        decreases
            N - i
    {
        i = i + 1;
        assert(0 <= i <= N);  // Help the verifier with the invariant
    }
    
    assert(i == N);  // Help prove the postcondition
    i
}

}