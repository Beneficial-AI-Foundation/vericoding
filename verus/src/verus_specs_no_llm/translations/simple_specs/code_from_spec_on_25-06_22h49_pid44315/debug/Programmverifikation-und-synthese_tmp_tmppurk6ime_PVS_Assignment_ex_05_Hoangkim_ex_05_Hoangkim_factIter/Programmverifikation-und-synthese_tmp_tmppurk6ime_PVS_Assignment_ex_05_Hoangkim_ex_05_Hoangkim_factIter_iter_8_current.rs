use builtin::*;
use builtin_macros::*;

verus! {

spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * fact(n - 1)
    }
}

fn main() {
}

fn factIter(n: nat) -> (a: nat)
    ensures
        a == fact(n)
{
    let mut result: nat = 1;
    let mut i: nat = 0;
    
    while i < n
        invariant
            result == fact(i),
            0 <= i <= n
        decreases n - i
    {
        i = i + 1;
        
        // Prove that fact(i) == i * fact(i - 1) when i > 0
        assert(i > 0);
        assert(fact(i) == i * fact(i - 1)) by {
            // This follows directly from the definition of fact when i > 0
        };
        
        // Update result
        result = result * i;
        
        // Prove that the invariant is maintained
        assert(result == fact(i)) by {
            // Before multiplication: result == fact(i-1) (from loop invariant)
            // After multiplication: result == fact(i-1) * i == fact(i)
        };
    }
    
    result
}

}