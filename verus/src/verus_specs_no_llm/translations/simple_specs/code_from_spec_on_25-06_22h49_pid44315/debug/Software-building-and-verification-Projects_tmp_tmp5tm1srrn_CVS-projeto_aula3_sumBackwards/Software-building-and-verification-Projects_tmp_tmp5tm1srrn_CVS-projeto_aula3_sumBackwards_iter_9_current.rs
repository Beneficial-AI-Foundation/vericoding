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

// Helper lemma to show the relationship between sum(n) and sum(i)
proof fn sum_split(n: nat, i: nat)
    requires i <= n
    ensures sum(n) == sum(n) - sum(i) + sum(i)
{
    // This is a tautology but helps Verus understand the arithmetic
}

fn sumBackwards(n: nat) -> (r: nat)
    ensures
        r == sum(n)
{
    let mut result = 0;
    let mut i = n;
    
    while i > 0
        invariant
            result == sum(n) - sum(i),
            i <= n
        decreases i
    {
        // Prove that sum(i) == i + sum(i-1) when i > 0
        sum_property(i);
        
        // The key insight: result + i will equal sum(n) - sum(i-1)
        // because result == sum(n) - sum(i) and sum(i) == i + sum(i-1)
        // so result + i == sum(n) - sum(i) + i == sum(n) - (i + sum(i-1)) + i == sum(n) - sum(i-1)
        
        result = result + i;
        i = i - 1;
    }
    
    // At loop exit: i == 0, so sum(i) == sum(0) == 0
    sum_zero();
    // Therefore result == sum(n) - sum(0) == sum(n) - 0 == sum(n)
    
    result
}

}