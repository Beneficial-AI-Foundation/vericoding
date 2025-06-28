use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    ensures k == n - (n % 7)
{
    proof {
        // We need to prove that n % 7 <= n to ensure the subtraction is valid
        assert(n % 7 <= n) by {
            // Use the fundamental property of modulo
            assert(n == (n / 7) * 7 + (n % 7));
            assert(n % 7 < 7);
            
            if n == 0 {
                assert(n % 7 == 0);
            } else {
                // For any n > 0, we have n / 7 * 7 >= 0
                // So n = (n / 7) * 7 + (n % 7) >= (n % 7)
                assert((n / 7) * 7 + (n % 7) >= (n % 7));
            }
        };
    }
    n - (n % 7)
}

fn test7(n: nat) -> (k: nat)
    ensures k == n - (n % 7)
{
    proof {
        // Same proof strategy
        assert(n % 7 <= n) by {
            assert(n == (n / 7) * 7 + (n % 7));
            assert(n % 7 < 7);
            
            if n == 0 {
                assert(n % 7 == 0);
            } else {
                assert((n / 7) * 7 + (n % 7) >= (n % 7));
            }
        };
    }
    n - (n % 7)
}

}