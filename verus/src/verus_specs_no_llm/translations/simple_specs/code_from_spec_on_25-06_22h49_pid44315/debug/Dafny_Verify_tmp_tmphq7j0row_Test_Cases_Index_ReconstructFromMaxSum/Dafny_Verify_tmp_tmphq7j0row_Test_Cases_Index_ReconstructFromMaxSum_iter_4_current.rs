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
        assert(y <= m);
        (x, y)
    } else {
        // This branch is actually unreachable given our precondition
        // If s - m > m, then s > 2*m, contradicting s <= 2*m
        assert(s - m > m);
        assert(s > 2 * m);
        assert(s <= 2 * m); // from precondition
        assert(false) by {
            assert(s > 2 * m);
            assert(s <= 2 * m);
        };
        let x = s - m;
        let y = m;
        (x, y)
    }
}

}