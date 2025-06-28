use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures
        s == x + y,
        m == if x >= y then x else y
{
    let sum = x + y;
    let max = if x >= y { x } else { y };
    (sum, max)
}

}