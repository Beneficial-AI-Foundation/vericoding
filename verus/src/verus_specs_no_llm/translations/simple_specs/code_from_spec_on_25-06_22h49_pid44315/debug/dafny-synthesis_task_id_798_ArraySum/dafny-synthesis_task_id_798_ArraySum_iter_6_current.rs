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
        a[(n - 1) as int] + sumTo(a, (n - 1) as nat)
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
    }
}

// Helper lemma for the loop invariant
proof fn sumFrom0To_step(a: Vec<int>, i: nat)
    requires i < a.len()
    ensures sumFrom0To(a, i + 1) == sumFrom0To(a, i) + a[i as int]
{
    // This follows directly from the definition of sumFrom0To
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
        // Prove the step relationship
        proof {
            assert(i < a.len());
            assert(i as nat < a.len());
            sumFrom0To_step(a, i as nat);
            assert(sumFrom0To(a, (i as nat) + 1) == sumFrom0To(a, i as nat) + a[i as int]);
        }
        
        sum = sum + a[i];
        i = i + 1;
        
        proof {
            assert(i as nat == (i - 1) as nat + 1);
        }
    }
    
    // After the loop, establish the postcondition
    proof {
        assert(i == a.len());
        assert(sum == sumFrom0To(a, a.len()));
        sumTo_equiv_sumFrom0To(a, a.len());
        assert(sumTo(a, a.len()) == sumFrom0To(a, a.len()));
    }
    
    sum
}

}