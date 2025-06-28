use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures
        s == x + y,
        (m == x || m == y) && x <= m && y <= m
{
    let sum = x + y;
    let max = if x >= y { x } else { y };
    (sum, max)
}

}