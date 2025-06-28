use builtin::*;
use builtin_macros::*;

verus! {

fn compute_values(n: i32) -> (a: i32, b: i32)
    requires
        n >= 0
    ensures
        a + b == 3 * n
{
    (3 * n, 0)
}

fn main() {
    // Example usage with proper exec function using concrete types
    let n: i32 = 5;
    let (a, b) = compute_values(n);
    
    // In Verus main, we use proof assertions
    proof {
        assert(a + b == 3 * n);
        assert(a + b == 15);
    }
}

}