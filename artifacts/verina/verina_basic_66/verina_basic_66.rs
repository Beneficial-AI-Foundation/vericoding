use vstd::prelude::*;

verus! {

// Precondition - always true
spec fn compute_is_even_precond(x: int) -> bool {
    true
}

// The main function that computes if x is even
fn compute_is_even(x: i32) -> (result: bool)
    requires compute_is_even_precond(x as int),
    ensures result == true <==> exists|k: int| #[trigger] (2 * k) == (x as int),
{
    let result = if x % 2 == 0 {
        true
    } else {
        false
    };
    
    proof {
        if result {
            // If result is true, then x % 2 == 0, so x is even
            let k = (x as int) / 2;
            assert((x as int) == 2 * k) by {
                // Use properties of modulo and division
                assert((x as int) % 2 == 0);
            }
        }
    }
    
    result
}

} // verus!

fn main() {}