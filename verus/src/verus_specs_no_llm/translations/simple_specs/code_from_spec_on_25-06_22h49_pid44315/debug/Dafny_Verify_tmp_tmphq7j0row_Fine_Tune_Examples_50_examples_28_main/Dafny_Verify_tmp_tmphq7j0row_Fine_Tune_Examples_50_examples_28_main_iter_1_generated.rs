use builtin::*;
use builtin_macros::*;

verus! {

fn main(x: int, y: int) -> (x_out: int, y_out: int, n: int)
    requires
        x >= 0,
        y >= 0,
        x == y
    ensures
        y_out == n
{
    // Since we need y_out == n, we can set both to any value
    // Let's use the input y (which equals x due to the precondition)
    (x, y, y)
}

}

The implementation satisfies all constraints:


The function is simple but correct - it returns the input values where `x_out = x`, `y_out = y`, and `n = y`, which satisfies the postcondition `y_out == n` since both equal `y`.