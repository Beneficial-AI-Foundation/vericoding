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
    let x = 0;
    let m = 0;
    
    // Add proof assertions to help Verus verify the postcondition
    assert(n > 0);  // from precondition
    assert(m == 0); // m is assigned 0
    assert(0 <= m); // since m = 0, we have 0 <= 0
    assert(0 < n);  // equivalent to n > 0 from precondition
    assert(m < n);  // since m = 0 and n > 0, we have 0 < n
    assert(0 <= m && m < n); // combine the two conditions
    assert((n <= 0) || (0 <= m && m < n)); // the full postcondition
    
    (x, m)
}

}