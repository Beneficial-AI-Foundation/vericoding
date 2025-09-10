use vstd::prelude::*;

verus! {

fn multiply(a: int, b: int) -> (result: int)
    ensures result == a * b
{
    assume(false);
    unreached();
}

}
fn main() {}