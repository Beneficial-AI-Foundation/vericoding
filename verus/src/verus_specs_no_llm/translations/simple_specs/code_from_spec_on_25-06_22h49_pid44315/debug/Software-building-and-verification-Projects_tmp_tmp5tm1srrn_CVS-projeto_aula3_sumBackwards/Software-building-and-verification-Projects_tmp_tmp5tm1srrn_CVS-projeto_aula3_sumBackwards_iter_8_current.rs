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

fn sumBackwards(n: nat) -> (r: nat)
    ensures
        r == sum(n)
{
    let mut result = 0;
    let mut i = n;
    
    while i > 0
        invariant
            result + sum(i) == sum(n),
            i <= n
        decreases i
    {
        // Prove that sum(i) == i + sum(i-1) when i > 0
        sum_property(i);
        
        // Update result and i
        result = result + i;
        i = i - 1;
    }
    
    // At loop exit: i == 0, so sum(i) == sum(0) == 0
    sum_zero();
    
    result
}

}