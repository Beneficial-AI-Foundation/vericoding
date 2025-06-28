use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures s == x + y
    ensures m == if x >= y { x } else { y }
{
    let s = x + y;
    let m = if x >= y { x } else { y };
    (s, m)
}

fn MaxSumCaller() -> (x: int, s: int, m: int)
    ensures s == x + x
    ensures m == x
{
    let x = 5;
    let (s, m) = MaxSum(x, x);
    (x, s, m)
}

}