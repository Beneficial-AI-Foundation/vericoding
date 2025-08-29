use vstd::prelude::*;

verus! {

// Precondition - always true in this case
spec fn min_of_three_precond(a: int, b: int, c: int) -> bool {
    true
}

// Postcondition - result is <= all inputs and equals one of them
spec fn min_of_three_postcond(a: int, b: int, c: int, result: int) -> bool {
    (result <= a && result <= b && result <= c) &&
    (result == a || result == b || result == c)
}

// The main function that finds minimum of three integers
fn min_of_three(a: int, b: int, c: int) -> (result: int)
    requires min_of_three_precond(a, b, c)
    ensures min_of_three_postcond(a, b, c, result)
{
    if a <= b && a <= c {
        a
    } else if b <= a && b <= c {
        b
    } else {
        c
    }
}

// Theorem stating that the specification is satisfied
proof fn min_of_three_spec_satisfied(a: int, b: int, c: int)
    requires min_of_three_precond(a, b, c)
    ensures ({
        let result = if a <= b && a <= c {
            a
        } else if b <= a && b <= c {
            b
        } else {
            c
        };
        min_of_three_postcond(a, b, c, result)
    })
{
    // The proof follows from case analysis
    if a <= b && a <= c {
        // Case 1: a is minimum
        assert(a <= a && a <= b && a <= c);
        assert(a == a);
    } else if b <= a && b <= c {
        // Case 2: b is minimum  
        assert(b <= a && b <= b && b <= c);
        assert(b == b);
    } else {
        // Case 3: c is minimum
        assert(!(a <= b && a <= c));
        assert(!(b <= a && b <= c));
        // From the negations above, we can derive that c is minimal
        assert(c <= a && c <= b && c <= c);
        assert(c == c);
    }
}

} // verus!

fn main() {}