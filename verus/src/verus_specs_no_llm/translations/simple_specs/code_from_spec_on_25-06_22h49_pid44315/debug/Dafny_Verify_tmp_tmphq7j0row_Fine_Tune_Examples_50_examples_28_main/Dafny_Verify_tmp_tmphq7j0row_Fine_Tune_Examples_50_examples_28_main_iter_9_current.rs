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
    let result = (x, x, x);
    
    // The postcondition y_out == n is satisfied because:
    // result.1 (y_out) == x and result.2 (n) == x
    // Therefore y_out == n
    assert(result.1 == result.2);
    
    result
}

}