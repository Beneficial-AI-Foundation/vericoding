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
    
    // Since the second component (x) = 0 and third component (y) = 0, 
    // we have x == 2 * y (0 == 2 * 0)
    assert(0 == 2 * 0);
    
    // The postcondition is satisfied because x == 2 * y is true
    // when x = 0 and y = 0
    assert((n % 2 != 0) || (0 == 2 * 0));
    
    result
}

}