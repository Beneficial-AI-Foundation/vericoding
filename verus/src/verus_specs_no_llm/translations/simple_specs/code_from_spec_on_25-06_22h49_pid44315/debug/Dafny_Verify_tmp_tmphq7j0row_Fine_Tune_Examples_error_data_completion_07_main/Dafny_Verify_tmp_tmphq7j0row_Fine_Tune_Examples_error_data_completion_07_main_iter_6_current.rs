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
    // Example usage with proper exec function
    let n: int = 5;
    let (a, b) = compute_values(n);
    
    // In Verus main, we use proof assertions
    proof {
        assert(a + b == 3 * n);
        assert(a + b == 15);
    }
    
    println!("a = {}, b = {}, sum = {}", a, b, a + b);
}

}