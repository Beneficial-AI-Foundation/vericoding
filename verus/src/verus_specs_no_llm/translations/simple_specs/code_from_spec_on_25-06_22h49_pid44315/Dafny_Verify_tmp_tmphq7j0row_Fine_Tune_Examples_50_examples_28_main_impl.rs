use builtin::*;
use builtin_macros::*;

verus! {

fn process_values(x: int, y: int) -> (int, int, int)
    requires
        x >= 0,
        y >= 0,
        x == y
    ensures
        process_values(x, y).1 == process_values(x, y).2
{
    // Since x == y from precondition, we can use either x or y
    // Let's return (x, x, x) to satisfy the postcondition
    let result = (x, x, x);
    
    // The postcondition is satisfied because:
    // result.1 (second element) == x and result.2 (third element) == x
    // Therefore the second and third elements are equal
    assert(result.1 == result.2);
    
    result
}

}