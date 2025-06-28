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
    // Example usage - explicitly specify int type
    let (a, b) = compute_values(5int);
    assert!(a + b == 15);
}

}