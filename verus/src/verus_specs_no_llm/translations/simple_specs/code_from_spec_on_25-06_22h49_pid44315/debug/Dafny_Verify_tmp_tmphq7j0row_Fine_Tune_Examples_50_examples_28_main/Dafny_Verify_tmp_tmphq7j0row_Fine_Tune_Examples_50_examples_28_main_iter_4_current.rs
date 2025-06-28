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
    // Since x == y from precondition, we can return any valid combination
    // where y_out == n. Let's return (x, y, y) which satisfies this.
    (x, y, y)
}

}