use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn compute_values(n: int) -> (x: int, m: int)
    requires
        n > 0
    ensures
        (n <= 0) || (0 <= m && m < n)
{
    // Since we have the precondition n > 0, the condition (n <= 0) in the postcondition
    // will be false, so we need to ensure (0 <= m && m < n)
    // We can return any valid values that satisfy this constraint
    let x = 0;
    let m = 0; // Since n > 0, we have 0 <= 0 < n, so this satisfies the constraint
    
    (x, m)
}

}