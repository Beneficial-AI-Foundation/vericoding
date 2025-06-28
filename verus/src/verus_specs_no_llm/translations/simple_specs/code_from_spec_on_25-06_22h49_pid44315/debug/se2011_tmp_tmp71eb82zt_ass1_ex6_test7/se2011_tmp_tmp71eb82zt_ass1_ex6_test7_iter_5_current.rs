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
            // The modulo operation always returns a value less than the divisor
            // and for natural numbers, n % 7 is always <= n
            let remainder = n % 7;
            assert(remainder < 7);
            
            // By the division algorithm: n = (n / 7) * 7 + (n % 7)
            // Since n / 7 >= 0 and n % 7 >= 0, we have n % 7 <= n
            if n < 7 {
                // When n < 7, n % 7 == n, so n % 7 <= n trivially
                assert(remainder == n);
            } else {
                // When n >= 7, n / 7 >= 1, so n = (n / 7) * 7 + remainder >= 7 + remainder > remainder
                assert(n >= 7);
                assert(remainder < 7);
                assert(n >= remainder);
            }
        };
    }
    n - (n % 7)
}

fn test7(n: nat) -> (k: nat)
    ensures k == n - (n % 7)
{
    proof {
        // Same proof as above
        assert(n % 7 <= n) by {
            let remainder = n % 7;
            assert(remainder < 7);
            
            if n < 7 {
                assert(remainder == n);
            } else {
                assert(n >= 7);
                assert(remainder < 7);
                assert(n >= remainder);
            }
        };
    }
    n - (n % 7)
}

}