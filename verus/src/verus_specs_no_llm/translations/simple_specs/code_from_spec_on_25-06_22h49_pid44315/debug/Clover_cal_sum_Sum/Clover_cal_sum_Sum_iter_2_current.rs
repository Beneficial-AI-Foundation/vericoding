// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Sum(N: int) -> (s: int)
    requires
        N >= 0
    ensures
        s == N * (N + 1) / 2
{
    let mut i: int = 0;
    let mut sum: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            sum == i * (i + 1) / 2
    {
        i = i + 1;
        sum = sum + i;
        
        // Proof that the invariant is maintained
        assert(sum == (i - 1) * ((i - 1) + 1) / 2 + i);
        assert(sum == (i - 1) * i / 2 + i);
        assert(sum == ((i - 1) * i + 2 * i) / 2);
        assert(sum == (i * (i - 1) + 2 * i) / 2);
        assert(sum == (i * (i - 1 + 2)) / 2);
        assert(sum == i * (i + 1) / 2);
    }
    
    sum
}

}