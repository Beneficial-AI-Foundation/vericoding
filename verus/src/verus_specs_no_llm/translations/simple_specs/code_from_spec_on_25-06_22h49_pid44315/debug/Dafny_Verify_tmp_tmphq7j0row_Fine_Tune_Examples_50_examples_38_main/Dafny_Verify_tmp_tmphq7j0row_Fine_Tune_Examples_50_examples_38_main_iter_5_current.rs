use builtin::*;
use builtin_macros::*;

verus! {

fn main(n: int) -> (i: int, x: int, y: int)
    requires
        n >= 0
    ensures
        (i % 2 != 0) || (x == 2 * y)
{
    let result = (n, 0, 0);
    let (i, x, y) = result;
    
    // Since x = 0 and y = 0, we have x == 2 * y (0 == 2 * 0)
    assert(x == 0 && y == 0);
    assert(2 * y == 2 * 0);
    assert(2 * y == 0);
    assert(x == 2 * y);
    
    // The postcondition is about the returned values
    // Since x == 2 * y is true, the disjunction (i % 2 != 0) || (x == 2 * y) is satisfied
    // regardless of whether i % 2 != 0
    assert((i % 2 != 0) || (x == 2 * y));
    
    result
}

}