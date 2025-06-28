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

fn TestingAbs2(x: int) -> (y: int)
    ensures 0 <= y,
    ensures x < 0 ==> y == -x,
    ensures x >= 0 ==> y == x,
{
    let result = Abs(x);
    // The assertions are redundant since they're already ensured by Abs's postconditions
    // But we can keep them for clarity
    assert(0 <= result);
    assert(x < 0 ==> result == -x);
    assert(x >= 0 ==> result == x);
    result
}

}