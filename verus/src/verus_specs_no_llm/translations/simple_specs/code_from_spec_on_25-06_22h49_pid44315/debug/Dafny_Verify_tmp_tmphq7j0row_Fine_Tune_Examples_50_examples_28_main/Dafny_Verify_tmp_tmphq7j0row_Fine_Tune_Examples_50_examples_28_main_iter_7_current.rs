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
    // Since x == y from precondition, we can use either x or y
    // Let's return (x, x, x) to satisfy y_out == n
    // Adding proof block to make the verification explicit
    proof {
        assert(x == y); // From precondition
    }
    (x, x, x)
}

}