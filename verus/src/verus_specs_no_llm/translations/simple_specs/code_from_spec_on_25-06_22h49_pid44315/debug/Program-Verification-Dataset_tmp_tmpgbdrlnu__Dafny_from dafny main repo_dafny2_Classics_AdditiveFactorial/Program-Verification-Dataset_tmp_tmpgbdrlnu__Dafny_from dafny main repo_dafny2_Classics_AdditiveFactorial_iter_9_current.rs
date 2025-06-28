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
                result == Factorial(sub(i, 1) as nat),
                n <= 20
        {
            // Prove the factorial property before updating
            assert(Factorial(i as nat) == (i as nat) * Factorial(sub(i, 1) as nat)) by {
                assert(i >= 1);
                assert(i as nat >= 1);
                assert(sub(i, 1) as nat == (i as nat) - 1);
            };
            
            result = result * i;
            
            // After multiplication, result now equals Factorial(i)
            assert(result == Factorial(i as nat));
            
            i = i + 1;
        }
        
        // After the loop, i == n + 1, so we computed Factorial(n)
        assert(i == n + 1);
        assert(sub(i, 1) as nat == n as nat);
        assert(result == Factorial(n as nat));
        
        result
    }
}

}