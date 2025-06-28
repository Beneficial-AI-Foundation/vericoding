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
            // Use the fundamental property of modulo: n = (n / 7) * 7 + (n % 7)
            assert(n == (n / 7) * 7 + (n % 7));
            // Since (n / 7) * 7 >= 0, we have n >= n % 7
            assert((n / 7) * 7 >= 0);
            // Therefore n = (n / 7) * 7 + (n % 7) >= 0 + (n % 7) = (n % 7)
        };
    }
    (n - (n % 7)) as nat
}

fn test7(n: nat) -> (k: nat)
    ensures k == n - (n % 7)
{
    proof {
        // Same proof strategy as Ceiling7
        assert(n % 7 <= n) by {
            assert(n == (n / 7) * 7 + (n % 7));
            assert((n / 7) * 7 >= 0);
        };
    }
    (n - (n % 7)) as nat
}

}