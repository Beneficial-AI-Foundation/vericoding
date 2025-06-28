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
    
    // These assertions help Verus verify the postconditions
    // From MaxSum ensures: s == x + y, where y == x, so s == x + x
    assert(s == x + x);
    
    // From MaxSum ensures: m == if x >= y { x } else { y }
    // Since x >= x is always true, m == x
    assert(x >= x); // This is always true
    assert(m == x);
    
    (x, s, m)
}

}