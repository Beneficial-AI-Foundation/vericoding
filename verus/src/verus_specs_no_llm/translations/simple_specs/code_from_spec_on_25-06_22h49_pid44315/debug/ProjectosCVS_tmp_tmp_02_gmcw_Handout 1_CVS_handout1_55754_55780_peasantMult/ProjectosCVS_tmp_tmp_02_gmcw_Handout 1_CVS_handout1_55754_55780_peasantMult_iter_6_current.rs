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
        };
        assert(b / 2 < b) by {
            assert(b >= 2);
        };
        assert(a * b == (2 * a) * (b / 2)) by {
            assert(b % 2 == 0);
            // For even numbers, b = 2 * (b / 2) is automatically handled by Verus
        };
        peasantMult(2 * a, b / 2)
    } else {
        // Odd case: a * b = a + (2*a) * ((b-1)/2)
        assert(b % 2 == 1);
        assert(b >= 1);
        assert(b >= 3) by {
            // Since b > 0, b != 1 (we're in else branch), and b % 2 == 1
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
        };
        assert((b - 1) / 2 < b) by {
            assert(b >= 3);
            assert((b - 1) / 2 <= (b - 1) / 2);
            assert((b - 1) < b);
        };
        assert(a * b == a + (2 * a) * ((b - 1) / 2)) by {
            // Mathematical reasoning for odd case
            assert(b == 1 + (b - 1));
            assert(a * b == a * (1 + (b - 1)));
            assert(a * (1 + (b - 1)) == a + a * (b - 1));
            // Since b-1 is even, we can use the fact that (b-1) = 2 * ((b-1)/2)
            assert(a * (b - 1) == a * (2 * ((b - 1) / 2)));
            assert(a * (2 * ((b - 1) / 2)) == (2 * a) * ((b - 1) / 2));
        };
        a + peasantMult(2 * a, (b - 1) / 2)
    }
}

}