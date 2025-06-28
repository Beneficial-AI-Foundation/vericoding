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
    
    // Proof assertions to help Verus verify the postconditions
    assert(s == x + x); // This follows from MaxSum's postcondition: s == x + y where y == x
    assert(m == x);     // This follows from MaxSum's postcondition: m == if x >= y { x } else { y } where y == x, so m == x
    
    (x, s, m)
}

}