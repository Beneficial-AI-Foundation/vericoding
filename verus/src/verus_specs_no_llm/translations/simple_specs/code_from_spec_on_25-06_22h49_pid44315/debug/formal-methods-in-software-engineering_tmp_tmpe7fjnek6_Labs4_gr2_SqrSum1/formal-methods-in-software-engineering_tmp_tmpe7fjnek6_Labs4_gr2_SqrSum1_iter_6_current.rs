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
        // Before the loop body: sum == SqrSumRec(old_i) where old_i = i - 1
        // After incrementing i: we have new i = old_i + 1
        // After updating sum: sum = old_sum + i * i = SqrSumRec(old_i) + i * i
        // Since i = old_i + 1 > 0, we have SqrSumRec(i) = i * i + SqrSumRec(i - 1)
        // And i - 1 = old_i, so SqrSumRec(i) = i * i + SqrSumRec(old_i)
        // Therefore sum = SqrSumRec(old_i) + i * i = SqrSumRec(i)
        
        assert(i > 0);
        assert(SqrSumRec(i) == i * i + SqrSumRec(i - 1));
    }
    
    sum
}

}