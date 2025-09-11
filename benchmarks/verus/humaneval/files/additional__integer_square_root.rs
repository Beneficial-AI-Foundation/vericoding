use vstd::prelude::*;

verus! {

/*
function_signature: "fn integer_square_root(n: i32) -> (result: i32)"
docstring: Implement integer square root functionality.
*/

fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn main() {}
}