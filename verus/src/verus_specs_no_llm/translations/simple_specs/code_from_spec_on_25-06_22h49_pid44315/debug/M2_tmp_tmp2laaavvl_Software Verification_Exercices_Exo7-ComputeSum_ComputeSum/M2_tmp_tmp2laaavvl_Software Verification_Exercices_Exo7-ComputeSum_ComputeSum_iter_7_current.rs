use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + Sum((n - 1) as nat) }
}

fn ComputeSum(n: nat) -> (s: nat)
    ensures
        s == Sum(n)
{
    let mut i: nat = 0;
    let mut sum: nat = 0;
    
    while i < n
        invariant 
            i <= n,
            sum == Sum(i)
        decreases n - i
    {
        i = i + 1;
        sum = sum + i;
        
        // Proof that sum == Sum(i) after the updates
        assert(sum == Sum(i)) by {
            // We need to show that sum == Sum(i)
            // Before the loop body: sum == Sum(i-1) (from invariant with old i)
            // After i = i + 1: we have new i = old_i + 1
            // After sum = sum + i: we have new sum = old_sum + new_i
            // So: new_sum = Sum(old_i) + new_i = Sum(i-1) + i
            // By definition: Sum(i) = i + Sum(i-1) when i > 0
            assert(i > 0);
            assert(Sum(i) == i + Sum((i - 1) as nat));
        }
    }
    
    sum
}

}

The key changes I made:




The verification should now pass because:
- The loop invariant is properly maintained
- The proof assertion correctly demonstrates why the invariant holds after each iteration
- The final result `sum` equals `Sum(n)` when the loop terminates with `i == n`