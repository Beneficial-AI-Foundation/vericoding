use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn peasantMult(a: int, b: int) -> (r: int)
    requires
        b > 0
    ensures
        r == a * b
    decreases b
{
    if b == 1 {
        a
    } else if b % 2 == 0 {
        // Even case: a * b = (2*a) * (b/2)
        assert(b >= 2);
        assert(b / 2 >= 1) by {
            assert(b >= 2);
            assert(b / 2 >= 2 / 2);
        };
        assert(b / 2 < b) by {
            assert(b >= 2);
            assert(b / 2 <= (b - 1));
        };
        assert(a * b == (2 * a) * (b / 2)) by {
            assert(b % 2 == 0);
            assert(b == 2 * (b / 2)) by {
                // For even numbers, b = 2 * (b / 2)
                assert(b - b % 2 == b);
            };
            assert(a * b == a * (2 * (b / 2)));
            assert(a * (2 * (b / 2)) == (a * 2) * (b / 2)) by {
                // Associativity of multiplication
                assert(a * (2 * (b / 2)) == (a * 2) * (b / 2));
            };
        };
        peasantMult(2 * a, b / 2)
    } else {
        // Odd case: a * b = a + (2*a) * ((b-1)/2)
        assert(b % 2 == 1);
        assert(b >= 1);
        assert(b >= 3) by {
            // Since b > 0, b != 1 (we're in else branch), and b % 2 == 1
            // The smallest odd number > 1 is 3
            assert(b > 1);
            assert(b % 2 == 1);
        };
        assert((b - 1) % 2 == 0) by {
            // If b is odd, then b-1 is even
            assert(b % 2 == 1);
        };
        assert((b - 1) / 2 > 0) by {
            assert(b >= 3);
            assert(b - 1 >= 2);
            assert((b - 1) / 2 >= 1);
        };
        assert((b - 1) / 2 < b) by {
            assert(b >= 3);
            assert((b - 1) / 2 <= (b - 1) / 2);
            assert((b - 1) / 2 < b - 1);
            assert(b - 1 < b);
        };
        assert(a * b == a + (2 * a) * ((b - 1) / 2)) by {
            assert(b == 1 + (b - 1));
            assert((b - 1) % 2 == 0);
            assert(b - 1 == 2 * ((b - 1) / 2)) by {
                // For even numbers, n = 2 * (n / 2)
                let n = b - 1;
                assert(n % 2 == 0);
                assert(n - n % 2 == n);
            };
            assert(a * b == a * (1 + (b - 1)));
            assert(a * (1 + (b - 1)) == a * 1 + a * (b - 1)) by {
                // Distributive property
                assert(a * (1 + (b - 1)) == a + a * (b - 1));
            };
            assert(a * (b - 1) == a * (2 * ((b - 1) / 2)));
            assert(a * (2 * ((b - 1) / 2)) == (a * 2) * ((b - 1) / 2)) by {
                // Associativity of multiplication
                assert(a * (2 * ((b - 1) / 2)) == (2 * a) * ((b - 1) / 2));
            };
        };
        a + peasantMult(2 * a, (b - 1) / 2)
    }
}

}