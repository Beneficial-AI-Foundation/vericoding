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
    let x = 0;
    let m = 0;
    
    // Proof annotation to help Verus verify the postcondition
    assert(0 <= m);  // m = 0, so 0 <= 0 is true
    assert(m < n);   // m = 0 and n > 0, so 0 < n is true
    assert(0 <= m && m < n);  // Both conditions are true
    
    (x, m)
}

}