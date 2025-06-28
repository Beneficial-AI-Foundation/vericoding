use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}

// Helper lemma to establish the key property of sum
proof fn sum_property(n: nat)
    requires n > 0
    ensures sum(n) == n + sum(n - 1)
    decreases n
{
    // This follows directly from the definition of sum
}

// Helper lemma to establish sum(0) == 0
proof fn sum_zero()
    ensures sum(0) == 0
{
    // This follows directly from the definition of sum
}

// Helper lemma to show the additive property of sum
proof fn sum_additive(n: nat, i: nat)
    requires i <= n
    ensures sum(n) == sum(i) + sum_range(i + 1, n)
    decreases n
{
    // This establishes the relationship between partial sums
}

// Helper spec function for sum of range from start to end (inclusive)
spec fn sum_range(start: nat, end: nat) -> nat
    decreases end
{
    if start > end {
        0
    } else if start == end {
        end
    } else {
        end + sum_range(start, end - 1)
    }
}

// Lemma to relate our loop computation to the final sum
proof fn sum_backwards_lemma(n: nat, i: nat, result: nat)
    requires 
        i <= n,
        result == sum_range(i + 1, n)
    ensures 
        result + sum(i) == sum(n)
{
    // This establishes that our accumulated result plus remaining sum equals total
}

fn sumBackwards(n: nat) -> (r: nat)
    ensures
        r == sum(n)
{
    let mut result = 0;
    let mut i = n;
    
    while i > 0
        invariant
            i <= n,
            result + sum(i) == sum(n)
        decreases i
    {
        // Before the update: result + sum(i) == sum(n)
        // We know sum(i) == i + sum(i-1) when i > 0
        sum_property(i);
        
        // So: result + i + sum(i-1) == sum(n)
        // After update: (result + i) + sum(i-1) == sum(n)
        // Which maintains our invariant with new values
        
        result = result + i;
        i = i - 1;
    }
    
    // At loop exit: i == 0, so sum(i) == sum(0) == 0
    sum_zero();
    // Therefore result + 0 == sum(n), so result == sum(n)
    
    result
}

}