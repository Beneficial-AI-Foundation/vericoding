use vstd::prelude::*;

verus! {

fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
{
    assume(false);
    unreached()
}

}
fn main() {}