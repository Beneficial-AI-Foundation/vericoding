use vstd::prelude::*;

verus! {

// Precondition for myMin - always true in this case
spec fn my_min_precond(x: int, y: int) -> bool {
    true
}

// Spec version of myMin for use in specifications
spec fn my_min_spec(x: int, y: int) -> int {
    if x < y { x } else { y }
}

// The executable myMin function
fn my_min(x: int, y: int) -> (result: int)
    requires my_min_precond(x, y)
    ensures 
        result == my_min_spec(x, y) &&
        (x <= y ==> result == x) && 
        (x > y ==> result == y)
{
    if x < y { x } else { y }
}

// Postcondition specification
spec fn my_min_postcond(x: int, y: int, result: int) -> bool {
    (x <= y ==> result == x) && (x > y ==> result == y)
}

// Theorem showing the function satisfies its specification
proof fn my_min_spec_satisfied(x: int, y: int)
    requires my_min_precond(x, y)
    ensures my_min_postcond(x, y, my_min_spec(x, y))
{
    // The proof is automatic since the postcondition matches the ensures clause
}

} // verus!

fn main() {}