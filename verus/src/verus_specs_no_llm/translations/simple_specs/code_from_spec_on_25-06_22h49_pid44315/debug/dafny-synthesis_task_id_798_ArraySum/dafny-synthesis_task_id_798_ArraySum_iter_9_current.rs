use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumTo(a: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        a[n - 1] + sumTo(a, n - 1)
    }
}

// Helper spec function that sums from 0 to n-1 (matches loop behavior)
spec fn sumFrom0To(a: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sumFrom0To(a, n - 1) + a[n - 1]
    }
}

// Proof function to establish equivalence between the two sum functions
proof fn sumTo_equiv_sumFrom0To(a: Vec<int>, n: nat)
    requires n <= a.len()
    ensures sumTo(a, n) == sumFrom0To(a, n)
    decreases n
{
    if n == 0 {
        // Base case: both return 0
    } else {
        // Inductive step
        assert(n >= 1);
        sumTo_equiv_sumFrom0To(a, n - 1);
        assert(sumTo(a, n - 1) == sumFrom0To(a, n - 1));
        assert(sumTo(a, n) == a[n - 1] + sumTo(a, n - 1));
        assert(sumFrom0To(a, n) == sumFrom0To(a, n - 1) + a[n - 1]);
    }
}

fn ArraySum(a: Vec<int>) -> (result: int)
    ensures
        result == sumTo(a, a.len())
{
    let mut sum = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == sumFrom0To(a, i as nat),
    {
        sum = sum + a[i];
        i = i + 1;
    }
    
    // After the loop, establish the postcondition
    sumTo_equiv_sumFrom0To(a, a.len());
    
    sum
}

}