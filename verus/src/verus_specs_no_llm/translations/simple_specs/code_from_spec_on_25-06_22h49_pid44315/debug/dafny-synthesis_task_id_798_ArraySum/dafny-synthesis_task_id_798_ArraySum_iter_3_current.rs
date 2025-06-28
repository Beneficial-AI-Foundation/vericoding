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
        a[n as int - 1] + sumTo(a, (n - 1) as nat)
    }
}

// Helper spec function that sums from 0 to n-1 (matches loop behavior)
spec fn sumFrom0To(a: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sumFrom0To(a, (n - 1) as nat) + a[(n - 1) as int]
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
        sumTo_equiv_sumFrom0To(a, (n - 1) as nat);
        // Both functions add a[n-1] to the sum of the first n-1 elements
        assert(sumTo(a, n) == a[n as int - 1] + sumTo(a, (n - 1) as nat));
        assert(sumFrom0To(a, n) == sumFrom0To(a, (n - 1) as nat) + a[(n - 1) as int]);
        // By induction hypothesis: sumTo(a, n-1) == sumFrom0To(a, n-1)
        assert(sumTo(a, n) == sumFrom0To(a, n));
    }
}

fn ArraySum(a: Vec<int>) -> (result: int)
    ensures
        result == sumTo(a, a.len())
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == sumFrom0To(a, i)
    {
        // The relationship we need for the loop
        assert(sumFrom0To(a, i + 1) == sumFrom0To(a, i) + a[i as int]);
        
        sum = sum + a[i as int];
        i = i + 1;
    }
    
    // After the loop, establish the postcondition
    sumTo_equiv_sumFrom0To(a, a.len());
    assert(sum == sumFrom0To(a, a.len()));
    assert(sumFrom0To(a, a.len()) == sumTo(a, a.len()));
    
    return sum;
}

}