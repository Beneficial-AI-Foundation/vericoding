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
    
    // To prove max1 == 5, we reason about the disjunction
    assert(max1 == 5) by {
        // We know max1 == 5 || max1 == 3 from the postcondition
        // We also know max1 >= 5
        // If max1 == 3, then 3 >= 5, which is false
        // Therefore max1 must equal 5
        if max1 == 3 {
            assert(max1 >= 5); // This gives us 3 >= 5
            assert(false); // Contradiction
        }
    };
    
    let max2 = Max(-2, 7);
    assert(max2 >= -2);
    assert(max2 >= 7);
    assert(max2 == -2 || max2 == 7);
    
    // Similar reasoning for max2
    assert(max2 == 7) by {
        // We know max2 == -2 || max2 == 7 from the postcondition
        // We also know max2 >= 7
        // If max2 == -2, then -2 >= 7, which is false
        // Therefore max2 must equal 7
        if max2 == -2 {
            assert(max2 >= 7); // This gives us -2 >= 7
            assert(false); // Contradiction
        }
    };
    
    let max3 = Max(0, 0);
    assert(max3 >= 0);
    assert(max3 == 0 || max3 == 0);
    assert(max3 == 0);
    
    true
}

}