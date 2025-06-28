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
    // Proof: Max(5, 3) returns 5 because 5 >= 3
    assert(max1 >= 5 && max1 >= 3 && (max1 == 5 || max1 == 3));
    assert(max1 == 5);
    
    let max2 = Max(-2, 7);
    // Proof: Max(-2, 7) returns 7 because 7 >= -2
    assert(max2 >= -2 && max2 >= 7 && (max2 == -2 || max2 == 7));
    assert(max2 == 7);
    
    let max3 = Max(0, 0);
    // Proof: Max(0, 0) returns 0 because both values are equal
    assert(max3 >= 0 && max3 >= 0 && (max3 == 0 || max3 == 0));
    assert(max3 == 0);
    
    true
}

}