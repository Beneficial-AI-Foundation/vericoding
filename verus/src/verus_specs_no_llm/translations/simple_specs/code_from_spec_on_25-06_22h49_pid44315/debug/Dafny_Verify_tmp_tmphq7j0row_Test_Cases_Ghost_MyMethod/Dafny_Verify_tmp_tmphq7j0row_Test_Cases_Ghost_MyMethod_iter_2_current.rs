use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MyMethod(x: int) -> (y: int)
    requires
        10 <= x
    ensures
        25 <= y
{
    let result = x + 15;
    assert(10 + 15 == 25);
    assert(x >= 10);
    assert(result >= 25);
    result
}

}