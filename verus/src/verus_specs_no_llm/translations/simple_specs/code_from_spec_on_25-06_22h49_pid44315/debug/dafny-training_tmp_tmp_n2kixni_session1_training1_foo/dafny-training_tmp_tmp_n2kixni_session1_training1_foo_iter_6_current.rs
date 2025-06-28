use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn abs(x: int) -> (y: int)
    ensures y >= 0 && (x >= 0 ==> y == x) && (x < 0 ==> y == -x)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

fn foo(x: int) -> (result: int)
    requires x >= 0
    ensures result >= 0
{
    let temp = abs(x);
    assert(temp >= 0); // This follows from the postcondition of abs
    assert(x >= 0 ==> temp == x); // This also follows from abs postcondition
    assert(temp == x); // Since x >= 0 from precondition
    temp
}

}