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
    
    // To prove max1 == 5, we need to show that max1 != 3
    // We know max1 >= 5, so if max1 == 3, we'd have 3 >= 5, which is false
    assert(max1 != 3) by {
        if max1 == 3 {
            assert(max1 >= 5); // 3 >= 5 is false
            assert(false);
        }
    };
    assert(max1 == 5) by {
        assert(max1 == 5 || max1 == 3);
        assert(max1 != 3);
    };
    
    let max2 = Max(-2, 7);
    assert(max2 >= -2);
    assert(max2 >= 7);
    assert(max2 == -2 || max2 == 7);
    
    // Similar reasoning for max2
    assert(max2 != -2) by {
        if max2 == -2 {
            assert(max2 >= 7); // -2 >= 7 is false
            assert(false);
        }
    };
    assert(max2 == 7) by {
        assert(max2 == -2 || max2 == 7);
        assert(max2 != -2);
    };
    
    let max3 = Max(0, 0);
    assert(max3 >= 0);
    assert(max3 == 0 || max3 == 0);
    assert(max3 == 0);
    
    true
}

}