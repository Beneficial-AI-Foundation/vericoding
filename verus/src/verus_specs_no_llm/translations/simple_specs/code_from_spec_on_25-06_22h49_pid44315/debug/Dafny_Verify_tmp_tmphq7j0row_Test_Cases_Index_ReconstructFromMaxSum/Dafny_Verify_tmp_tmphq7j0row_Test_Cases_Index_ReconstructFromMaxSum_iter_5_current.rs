use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReconstructFromMaxSum(s: int, m: int) -> (x: int, y: int)
    requires
        s <= 2 * m
    ensures
        s == (x + y),
        (m == x || m == y) && x <= m && y <= m
{
    if s - m <= m {
        let x = m;
        let y = s - m;
        // Prove that y <= m
        assert(y == s - m);
        assert(s <= 2 * m);  // from precondition
        assert(y <= m) by {
            assert(s - m <= m);  // from if condition
            assert(y == s - m);
        };
        (x, y)
    } else {
        // This branch is unreachable given our precondition
        // If s - m > m, then s > 2*m, contradicting s <= 2*m
        assert(s - m > m);
        assert(s > 2 * m) by {
            assert(s - m > m);
            assert(s == (s - m) + m);
        };
        // This contradicts our precondition s <= 2 * m
        assert(false) by {
            assert(s > 2 * m);
            assert(s <= 2 * m);  // from precondition
        };
        // The rest is unreachable, but we need to return something
        (0, 0)  // arbitrary values since this is unreachable
    }
}

}