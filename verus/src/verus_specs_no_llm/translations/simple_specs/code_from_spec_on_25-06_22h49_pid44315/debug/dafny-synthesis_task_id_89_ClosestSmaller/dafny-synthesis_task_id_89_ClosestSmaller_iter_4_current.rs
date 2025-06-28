use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ClosestSmaller(n: int) -> (m: int)
    requires
        n > 0
    ensures
        m + 1 == n
{
    let result = n - 1;
    // Verus can automatically prove this with integer arithmetic
    assert(result + 1 == n) by {
        // The proof is automatic for integer arithmetic
    };
    result
}

}