use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StarNumber(n: int) -> (star: int)
    requires
        n >= 0
    ensures
        star == 6 * n * (n - 1) + 1
{
    let result = 6 * n * (n - 1) + 1;
    result
}

}

The implementation is straightforward since we're directly computing the formula specified in the postcondition. The function:


Since we're working with mathematical integers (`int` type) in Verus, the arithmetic is exact and there are no overflow concerns. The verification should succeed because the returned value is literally the same expression as required in the ensures clause.