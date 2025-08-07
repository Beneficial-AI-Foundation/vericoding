use vstd::prelude::*;

verus! {

// Precondition for swap - always true in this case
spec fn swap_precond(x: int, y: int) -> bool {
    true
}

// Postcondition for swap
spec fn swap_postcond(x: int, y: int, result: (int, int)) -> bool {
    result.0 == y && result.1 == x &&
    (x != y ==> (result.0 != x && result.1 != y))
}

// The swap function
fn swap(x: int, y: int) -> (result: (int, int))
    requires swap_precond(x, y),
    ensures swap_postcond(x, y, result),
{
    let tmp = x;
    let new_x = y;
    let new_y = tmp;
    (new_x, new_y)
}

} // verus!

fn main() {}