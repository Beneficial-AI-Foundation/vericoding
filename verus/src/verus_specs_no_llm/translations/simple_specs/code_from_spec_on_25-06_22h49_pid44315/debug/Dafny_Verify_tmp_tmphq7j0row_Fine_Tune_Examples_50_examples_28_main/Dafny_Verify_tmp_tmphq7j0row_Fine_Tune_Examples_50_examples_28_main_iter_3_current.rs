use builtin::*;
use builtin_macros::*;

verus! {

fn process_values(x: int, y: int) -> (x_out: int, y_out: int, n: int)
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