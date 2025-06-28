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
        assert(y <= m) by {
            assert(s - m <= m);
        };
        (x, y)
    } else {
        let x = s - m;
        let y = m;
        assert(x <= m) by {
            // If s - m > m, then s > 2*m, but we have s <= 2*m
            // This is a contradiction, so this branch is unreachable
            assert(s - m > m);
            assert(s > 2 * m);
            assert(false);
        };
        (x, y)
    }
}

}