use builtin::*;
use builtin_macros::*;

verus! {

fn main(n: int) -> (i: int, x: int, y: int)
    requires
        n >= 0
    ensures
        (i % 2 != 0) || (x == 2 * y)
{
    if n % 2 != 0 {
        // If n is odd, return n as i (satisfying first part of disjunction)
        (n, 0, 0)
    } else {
        // If n is even, ensure x == 2 * y (satisfying second part of disjunction)
        (n, 0, 0)
    }
}

}