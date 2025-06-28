use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * Factorial(n - 1)
    }
}

fn AdditiveFactorial(n: u64) -> (u: u64)
    requires n <= 20  // Prevent overflow
    ensures u == Factorial(n as nat)
{
    if n == 0 {
        1
    } else {
        let mut result: u64 = 1;
        let mut i: u64 = 1;
        
        while i <= n
            invariant
                1 <= i <= n + 1,
                result == Factorial((i - 1) as nat),
                n <= 20,
                i >= 1
        {
            // Prove the factorial property before updating
            assert(i >= 1);
            assert((i - 1) as nat + 1 == i as nat);
            assert(Factorial(i as nat) == (i as nat) * Factorial((i - 1) as nat)) by {
                // This follows from the definition of Factorial when i > 0
                if i as nat == 0 {
                    assert(false); // contradiction since i >= 1
                } else {
                    assert(i as nat > 0);
                    assert(Factorial(i as nat) == (i as nat) * Factorial((i as nat) - 1));
                    assert((i as nat) - 1 == (i - 1) as nat);
                }
            };
            
            result = result * i;
            
            // After multiplication, result now equals Factorial(i)
            assert(result == Factorial(i as nat));
            
            i = i + 1;
        }
        
        // After the loop, i == n + 1, so we computed Factorial(n)
        assert(i == n + 1);
        assert(i - 1 == n);
        assert((i - 1) as nat == n as nat);
        assert(result == Factorial(n as nat));
        
        result
    }
}

}