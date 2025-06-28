use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn double_quadruple(x: i32) -> (a: i32, b: i32)
    requires
        x <= 536870911 && x >= -536870912  // Ensure no overflow: 4 * x fits in i32
    ensures
        a == 2 * x && b == 4 * x
{
    let result_a = x + x;  // Use addition instead of multiplication to avoid overflow issues
    let result_b = result_a + result_a;  // 4 * x = 2 * (2 * x)
    
    // Add proof assertions to help verification
    assert(result_a == 2 * x);
    assert(result_b == 4 * x);
    
    (result_a, result_b)
}

}