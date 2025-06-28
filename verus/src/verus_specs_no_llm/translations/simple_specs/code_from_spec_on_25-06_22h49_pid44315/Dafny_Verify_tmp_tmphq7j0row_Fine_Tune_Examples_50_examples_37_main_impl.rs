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
    
    // Since n > 0 (from precondition), we need to prove 0 <= m && m < n
    // m = 0, so 0 <= m is trivially true
    // n > 0 and m = 0, so m < n is true
    
    (x, m)
}

}