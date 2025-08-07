use vstd::prelude::*;

verus! {

// Precondition for maxOfThree - trivially true
spec fn max_of_three_precond(a: int, b: int, c: int) -> bool {
    true
}

// Spec version of the maxOfThree function
spec fn max_of_three_spec(a: int, b: int, c: int) -> int {
    if a >= b && a >= c {
        a
    } else if b >= a && b >= c {
        b
    } else {
        c
    }
}

// The maxOfThree function
fn max_of_three(a: int, b: int, c: int) -> (result: int)
    requires max_of_three_precond(a, b, c),
    ensures 
        result == max_of_three_spec(a, b, c) &&
        (result >= a && result >= b && result >= c) &&
        (result == a || result == b || result == c),
{
    if a >= b && a >= c {
        a
    } else if b >= a && b >= c {
        b
    } else {
        c
    }
}

// Postcondition specification
spec fn max_of_three_postcond(a: int, b: int, c: int, result: int) -> bool {
    (result >= a && result >= b && result >= c) && 
    (result == a || result == b || result == c)
}

// Theorem that demonstrates the function satisfies its specification
proof fn max_of_three_spec_satisfied(a: int, b: int, c: int) 
    requires max_of_three_precond(a, b, c),
    ensures max_of_three_postcond(a, b, c, max_of_three_spec(a, b, c)),
{
    // The proof follows from the definition of max_of_three_spec
}

}

fn main() {}