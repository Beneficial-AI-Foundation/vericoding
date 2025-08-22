use vstd::prelude::*;

verus! {

// Precondition function
spec fn abs_precond(x: int) -> bool {
    true
}

// Postcondition function  
spec fn abs_postcond(x: int, result: int) -> bool {
    (x >= 0 ==> x == result) && (x < 0 ==> x + result == 0)
}

// The absolute value function as a spec function
spec fn abs_spec(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

// Proof that the spec satisfies the postcondition
proof fn abs_spec_satisfied(x: int)
    requires abs_precond(x)
    ensures abs_postcond(x, abs_spec(x))
{
    if x >= 0 {
        assert(abs_spec(x) == x);
        assert(x == abs_spec(x));
    } else {
        assert(abs_spec(x) == -x);
        assert(x + abs_spec(x) == x + (-x));
        assert(x + abs_spec(x) == 0);
    }
}

fn main() {}

} // verus!