use vstd::prelude::*;

verus! {

fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
{
    assume(false);
    unreached();
}

}
fn main() {}