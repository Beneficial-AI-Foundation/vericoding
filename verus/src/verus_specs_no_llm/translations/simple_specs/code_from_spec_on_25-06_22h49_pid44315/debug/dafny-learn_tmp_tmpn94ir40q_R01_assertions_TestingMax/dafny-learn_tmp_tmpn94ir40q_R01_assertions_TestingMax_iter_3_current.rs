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
    // The postconditions of Max give us: max1 >= 5, max1 >= 3, max1 == 5 || max1 == 3
    // Since 5 >= 3, we know Max(5, 3) should return 5
    assert(max1 >= 5 && max1 >= 3 && (max1 == 5 || max1 == 3));
    // To prove max1 == 5, we use the fact that max1 >= 5 and max1 == 5 || max1 == 3
    // If max1 == 3, then max1 >= 5 would be false, so max1 must be 5
    assert(max1 == 5);
    
    let max2 = Max(-2, 7);
    // The postconditions give us: max2 >= -2, max2 >= 7, max2 == -2 || max2 == 7
    assert(max2 >= -2 && max2 >= 7 && (max2 == -2 || max2 == 7));
    // Since max2 >= 7 and max2 == -2 || max2 == 7, and -2 < 7, max2 must be 7
    assert(max2 == 7);
    
    let max3 = Max(0, 0);
    // The postconditions give us: max3 >= 0, max3 >= 0, max3 == 0 || max3 == 0
    assert(max3 >= 0 && max3 >= 0 && (max3 == 0 || max3 == 0));
    assert(max3 == 0);
    
    true
}

}