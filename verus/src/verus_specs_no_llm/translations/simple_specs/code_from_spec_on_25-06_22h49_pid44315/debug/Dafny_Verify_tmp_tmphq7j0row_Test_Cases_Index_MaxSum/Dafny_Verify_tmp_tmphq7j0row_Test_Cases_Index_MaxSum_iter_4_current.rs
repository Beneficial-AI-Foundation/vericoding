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
    let s = x + y;
    let m = if x >= y { x } else { y };
    (s, m)
}

}