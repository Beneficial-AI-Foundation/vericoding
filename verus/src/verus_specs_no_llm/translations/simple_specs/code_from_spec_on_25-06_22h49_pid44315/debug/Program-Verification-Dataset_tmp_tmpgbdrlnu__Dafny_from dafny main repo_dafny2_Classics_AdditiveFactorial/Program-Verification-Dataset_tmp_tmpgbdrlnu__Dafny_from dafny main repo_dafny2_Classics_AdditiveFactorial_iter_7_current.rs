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
                i <= 21  // Needed for overflow safety
        {
            // Prove that result * i will equal Factorial(i)
            assert(i >= 1);
            assert(i as nat >= 1);
            assert(Factorial(i as nat) == (i as nat) * Factorial((i - 1) as nat));
            
            result = result * i;
            i = i + 1;
        }
        
        // After the loop, i == n + 1, so result == Factorial(n)
        assert(i == n + 1);
        assert((i - 1) as nat == n as nat);
        
        result
    }
}

}