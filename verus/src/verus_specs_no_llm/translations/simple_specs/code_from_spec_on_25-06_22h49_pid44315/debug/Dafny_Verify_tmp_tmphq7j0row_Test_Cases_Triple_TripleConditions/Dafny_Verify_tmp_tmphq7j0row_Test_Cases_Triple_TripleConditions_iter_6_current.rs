use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn triple_conditions(x: int) -> (r: int)
    requires
        x % 2 == 0
    ensures
        r == 3 * x
{
    let result = 3 * x;
    assert(result == 3 * x);
    result
}

}

Actually, the original implementation should verify correctly as is. The simpler version should work:

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn triple_conditions(x: int) -> (r: int)
    requires
        x % 2 == 0
    ensures
        r == 3 * x
{
    3 * x
}

}

The function is mathematically sound: given any even integer `x` (as required by the precondition `x % 2 == 0`), returning `3 * x` directly satisfies the postcondition `r == 3 * x`. The precondition about `x` being even doesn't affect the correctness of the multiplication operation itself.