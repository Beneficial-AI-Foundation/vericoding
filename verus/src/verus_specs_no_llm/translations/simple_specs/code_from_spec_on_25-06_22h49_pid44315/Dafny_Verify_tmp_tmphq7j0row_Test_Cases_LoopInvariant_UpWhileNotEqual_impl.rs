use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn up_while_not_equal(N: int) -> (i: int)
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
        // Add proof that i <= N after increment
        assert(i <= N) by {
            // The loop condition ensures i != N before increment
            // Combined with invariant i <= N, we have i < N
            // Therefore i + 1 <= N
        };
    }
    
    // After loop exits, we have !(i != N), which means i == N
    assert(i == N);
    i
}

}