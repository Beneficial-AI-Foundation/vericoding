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
    6 * n * (n - 1) + 1
}

}

The implementation directly computes `6 * n * (n - 1) + 1`, which satisfies the postcondition by definition. Since we're working with mathematical integers (`int` type) in Verus, there are no overflow concerns, and the arithmetic operations are exact.