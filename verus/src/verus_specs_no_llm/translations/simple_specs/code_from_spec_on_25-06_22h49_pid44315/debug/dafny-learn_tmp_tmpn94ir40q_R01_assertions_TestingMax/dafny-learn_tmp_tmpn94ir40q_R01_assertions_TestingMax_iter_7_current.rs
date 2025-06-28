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
    assert(max1 >= 5);
    assert(max1 >= 3);
    assert(max1 == 5 || max1 == 3);
    
    // To prove max1 == 5, we use proof by contradiction
    assert(max1 == 5) by {
        if max1 != 5 {
            // Since max1 == 5 || max1 == 3, and max1 != 5, we must have max1 == 3
            assert(max1 == 3);
            // But we also know max1 >= 5, so 3 >= 5, which is a contradiction
            assert(3 >= 5);
            assert(false);
        }
    };
    
    let max2 = Max(-2, 7);
    assert(max2 >= -2);
    assert(max2 >= 7);
    assert(max2 == -2 || max2 == 7);
    
    // Similar reasoning for max2
    assert(max2 == 7) by {
        if max2 != 7 {
            // Since max2 == -2 || max2 == 7, and max2 != 7, we must have max2 == -2
            assert(max2 == -2);
            // But we also know max2 >= 7, so -2 >= 7, which is a contradiction
            assert(-2 >= 7);
            assert(false);
        }
    };
    
    let max3 = Max(0, 0);
    assert(max3 >= 0);
    assert(max3 == 0 || max3 == 0);
    assert(max3 == 0);
    
    true
}

}