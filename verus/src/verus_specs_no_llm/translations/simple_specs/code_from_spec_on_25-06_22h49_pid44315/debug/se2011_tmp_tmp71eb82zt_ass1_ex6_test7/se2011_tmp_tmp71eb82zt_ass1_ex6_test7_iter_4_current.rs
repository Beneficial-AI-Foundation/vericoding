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
            if n == 0 {
                assert(0 % 7 == 0);
            } else {
                // For any positive integer n, n % 7 < 7 <= n when n >= 7
                // When n < 7, n % 7 == n, so n % 7 <= n
                assert(n % 7 < 7) by {
                    mod_range(n as int, 7);
                };
                if n >= 7 {
                    assert(7 <= n);
                    assert(n % 7 < 7 <= n);
                } else {
                    assert(n % 7 == n) by {
                        small_mod(n as int, 7);
                    };
                    assert(n % 7 <= n);
                }
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
            if n == 0 {
                assert(0 % 7 == 0);
            } else {
                assert(n % 7 < 7) by {
                    mod_range(n as int, 7);
                };
                if n >= 7 {
                    assert(7 <= n);
                    assert(n % 7 < 7 <= n);
                } else {
                    assert(n % 7 == n) by {
                        small_mod(n as int, 7);
                    };
                    assert(n % 7 <= n);
                }
            }
        };
    }
    n - (n % 7)
}

}