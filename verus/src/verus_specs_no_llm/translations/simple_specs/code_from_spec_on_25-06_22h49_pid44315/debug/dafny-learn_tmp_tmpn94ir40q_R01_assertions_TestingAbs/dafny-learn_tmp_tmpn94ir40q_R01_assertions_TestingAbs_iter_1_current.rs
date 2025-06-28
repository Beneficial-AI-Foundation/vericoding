use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Abs(x: int) -> (y: int)
    ensures 0 <= y,
    ensures x < 0 ==> y == -x,
    ensures x >= 0 ==> y == x,
{
    if x < 0 {
        -x
    } else {
        x
    }
}

// Test method that calls Abs and verifies its properties
method TestingAbs()
{
    let result1 = Abs(5);
    assert(result1 == 5);
    
    let result2 = Abs(-3);
    assert(result2 == 3);
    
    let result3 = Abs(0);
    assert(result3 == 0);
}

}