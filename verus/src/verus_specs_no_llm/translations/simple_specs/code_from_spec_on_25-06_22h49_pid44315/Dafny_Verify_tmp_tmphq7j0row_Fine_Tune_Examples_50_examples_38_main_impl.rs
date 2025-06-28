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
        // Since n is odd, n % 2 != 0, so i % 2 != 0 will be true
        (n, 0, 0)
    } else {
        // If n is even, ensure x == 2 * y (satisfying second part of disjunction)
        // We can set x = 4 and y = 2, so x == 2 * y
        (n, 4, 2)
    }
}

}