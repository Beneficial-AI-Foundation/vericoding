use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(a: int, b: int) -> (c: int)
    ensures c >= a,
    ensures c >= b,
    ensures c == a || c == b,
{
    if a >= b {
        a
    } else {
        b
    }
}

fn TestingMax() -> (result: bool)
    ensures result == true,
{
    let max1 = Max(5, 3);
    let max2 = Max(-2, 7);
    let max3 = Max(0, 0);
    
    // These assertions verify our Max function works correctly
    assert(max1 == 5);
    assert(max2 == 7);
    assert(max3 == 0);
    
    true
}

}