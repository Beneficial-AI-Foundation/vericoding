use builtin::*;
use builtin_macros::*;

verus! {

fn compute_values(n: int) -> (a: int, b: int)
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
    let (a, b) = compute_values(n as int);
    
    // In Verus main, we use proof assertions
    proof {
        assert(a + b == 3 * (n as int));
        assert(a + b == 15);
    }
    
    // Simple print statement for Verus
    print_integer(a + b);
}

// Helper function for printing (since println! might not be available in all Verus contexts)
fn print_integer(x: int) {
    // This is a stub - in real Verus you'd use appropriate output methods
}

}