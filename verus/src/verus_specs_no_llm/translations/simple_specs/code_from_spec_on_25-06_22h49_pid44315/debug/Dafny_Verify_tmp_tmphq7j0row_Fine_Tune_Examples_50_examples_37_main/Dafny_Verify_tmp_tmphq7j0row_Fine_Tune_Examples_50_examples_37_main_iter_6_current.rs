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
    
    // From precondition: n > 0
    // We set m = 0, so:
    // - 0 <= m is true (since m == 0)
    // - m < n is true (since 0 < n)
    // Therefore (0 <= m && m < n) is true
    // Making the entire postcondition true
    
    assert(m == 0);
    assert(0 <= m);
    assert(n > 0);
    assert(0 < n);  // Equivalent to n > 0
    assert(m < n);  // Since m == 0 and n > 0
    assert(0 <= m && m < n);
    
    (x, m)
}

}