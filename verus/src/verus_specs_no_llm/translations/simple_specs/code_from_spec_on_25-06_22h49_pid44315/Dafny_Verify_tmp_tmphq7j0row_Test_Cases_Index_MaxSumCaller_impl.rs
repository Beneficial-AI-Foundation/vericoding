use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures s == x + y,
    ensures m == if x >= y { x } else { y },
{
    let s = x + y;
    let m = if x >= y { x } else { y };
    (s, m)
}

fn MaxSumCaller() -> (x: int, s: int, m: int)
    ensures s == x + x,
    ensures m == x,
{
    let x = 5;
    let (s, m) = MaxSum(x, x);
    
    // The postconditions should be automatically satisfied by the ensures clauses of MaxSum
    // Since we call MaxSum(x, x), we have:
    // - s == x + x (from MaxSum's first postcondition)
    // - m == if x >= x { x } else { x } == x (from MaxSum's second postcondition)
    
    (x, s, m)
}

}