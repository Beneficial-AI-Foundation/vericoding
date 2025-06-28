use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SqrSumRec(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        n * n + SqrSumRec(n - 1)
    }
}

fn SqrSum1(n: int) -> (s: int)
    requires
        n >= 0
    ensures
        s == SqrSumRec(n)
{
    let mut i = 0;
    let mut sum = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            sum == SqrSumRec(i)
        decreases
            n - i
    {
        i = i + 1;
        sum = sum + i * i;
        
        // Proof that the invariant is maintained
        assert(sum == SqrSumRec(i - 1) + i * i);
        
        // We need to show that SqrSumRec(i) == i * i + SqrSumRec(i - 1)
        // This follows from the definition of SqrSumRec when i > 0
        assert(i > 0);
        assert(SqrSumRec(i) == i * i + SqrSumRec(i - 1)) by {
            // This follows directly from the definition of SqrSumRec
            // since i > 0, SqrSumRec(i) = i * i + SqrSumRec(i - 1)
        };
        
        assert(sum == SqrSumRec(i));
    }
    
    sum
}

}