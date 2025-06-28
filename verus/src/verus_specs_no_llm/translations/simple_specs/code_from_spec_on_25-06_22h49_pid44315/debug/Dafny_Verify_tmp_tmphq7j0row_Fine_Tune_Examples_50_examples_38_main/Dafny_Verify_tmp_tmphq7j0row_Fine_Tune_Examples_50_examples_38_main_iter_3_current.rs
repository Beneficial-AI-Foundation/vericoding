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
    
    // Prove that x == 2 * y
    assert(x == 2 * y);
    // Therefore the disjunction is satisfied
    assert((i % 2 != 0) || (x == 2 * y));
    
    result
}

}