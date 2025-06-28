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
            proof {
                // We need to prove that multiplying by i gives us Factorial(i)
                // Since result == Factorial(i-1) and we multiply by i,
                // we get result * i == Factorial(i-1) * i == Factorial(i)
                assert(i >= 1);
                assert(i as nat >= 1);
                assert(Factorial(i as nat) == (i as nat) * Factorial((i - 1) as nat)) by {
                    assert(i as nat > 0);
                };
                assert(result * i == Factorial((i - 1) as nat) * (i as nat));
                assert(Factorial((i - 1) as nat) * (i as nat) == Factorial(i as nat));
            }
            
            result = result * i;
            i = i + 1;
            
            proof {
                // After updating both result and i, we need to show the invariant holds
                // Now result == old(result) * old(i) == Factorial(old(i-1)) * old(i) == Factorial(old(i))
                // And i == old(i) + 1, so i - 1 == old(i)
                // Therefore result == Factorial((i-1))
                assert(result == Factorial((i - 1) as nat));
            }
        }
        
        proof {
            // After the loop, i == n + 1, so i - 1 == n
            assert(i == n + 1);
            assert((i - 1) as nat == n as nat);
            assert(result == Factorial(n as nat));
        }
        
        result
    }
}

}