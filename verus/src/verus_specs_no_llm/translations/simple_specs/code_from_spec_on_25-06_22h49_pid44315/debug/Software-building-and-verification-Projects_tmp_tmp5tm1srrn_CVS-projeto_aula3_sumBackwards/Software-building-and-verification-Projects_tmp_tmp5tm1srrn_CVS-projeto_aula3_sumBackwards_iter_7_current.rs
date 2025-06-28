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
    
    // Establish initial invariant
    assert(sum(n) - sum(n) == 0);
    assert(result == 0);
    
    while i > 0
        invariant
            result + sum(i) == sum(n),
            i <= n
        decreases i
    {
        // Before the update: result + sum(i) == sum(n)
        // We know that sum(i) == i + sum(i-1) when i > 0
        proof {
            sum_property(i);
        }
        assert(sum(i) == i + sum(i - 1));
        
        // So: result + i + sum(i-1) == sum(n)
        // Which means: (result + i) + sum(i-1) == sum(n)
        
        result = result + i;
        i = i - 1;
        
        // After the update: result_new + sum(i_new) == sum(n)
        // where result_new = result_old + i_old and i_new = i_old - 1
        assert(result + sum(i) == sum(n));
    }
    
    // At loop exit: i == 0
    assert(i == 0);
    proof {
        sum_zero();
    }
    assert(sum(0) == 0);
    
    // From invariant: result + sum(0) == sum(n)
    // Therefore: result + 0 == sum(n)
    // So: result == sum(n)
    assert(result + sum(i) == sum(n));
    assert(result == sum(n));
    
    result
}

}