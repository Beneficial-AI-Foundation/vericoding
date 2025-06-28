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
        (x, y)
    } else {
        let x = s - m;
        let y = m;
        (x, y)
    }
}

}