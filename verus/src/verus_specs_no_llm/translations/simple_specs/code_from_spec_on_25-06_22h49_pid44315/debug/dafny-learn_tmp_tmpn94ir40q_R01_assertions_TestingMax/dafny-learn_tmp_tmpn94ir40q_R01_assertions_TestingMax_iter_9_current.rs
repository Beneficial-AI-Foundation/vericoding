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
    
    // To prove max1 == 5, we use the fact that max1 >= 5 and max1 == 5 || max1 == 3
    assert(max1 == 5) by {
        // We know max1 >= 5 and (max1 == 5 || max1 == 3)
        // If max1 == 3, then we would have 3 >= 5, which is impossible
        // Therefore max1 == 5
        assert(max1 >= 5);
        assert(max1 == 5 || max1 == 3);
        // Verus can deduce that since 3 < 5, and max1 >= 5, max1 cannot be 3
    };
    
    let max2 = Max(-2, 7);
    assert(max2 >= -2);
    assert(max2 >= 7);
    assert(max2 == -2 || max2 == 7);
    
    // Similar reasoning for max2
    assert(max2 == 7) by {
        // We know max2 >= 7 and (max2 == -2 || max2 == 7)
        // If max2 == -2, then we would have -2 >= 7, which is impossible
        // Therefore max2 == 7
        assert(max2 >= 7);
        assert(max2 == -2 || max2 == 7);
        // Verus can deduce that since -2 < 7, and max2 >= 7, max2 cannot be -2
    };
    
    let max3 = Max(0, 0);
    assert(max3 >= 0);
    assert(max3 == 0 || max3 == 0);
    assert(max3 == 0);
    
    true
}

}