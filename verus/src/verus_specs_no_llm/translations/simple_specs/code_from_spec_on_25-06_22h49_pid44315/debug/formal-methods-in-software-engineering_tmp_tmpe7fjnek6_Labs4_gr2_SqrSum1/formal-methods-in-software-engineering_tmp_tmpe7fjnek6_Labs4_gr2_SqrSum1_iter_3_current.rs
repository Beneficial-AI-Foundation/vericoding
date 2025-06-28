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
        assert(sum == SqrSumRec(i)) by {
            // SqrSumRec(i) = i * i + SqrSumRec(i - 1) when i > 0
            assert(i > 0);
            assert(SqrSumRec(i) == i * i + SqrSumRec(i - 1));
        }
    }
    
    sum
}

}

The key insight is that the recursive specification `SqrSumRec(n)` computes the sum of squares from 1 to n, where:
- `SqrSumRec(0) = 0`
- `SqrSumRec(n) = n * n + SqrSumRec(n-1)` for n > 0

The loop implementation now correctly:

This matches the recursive specification perfectly and should verify correctly.