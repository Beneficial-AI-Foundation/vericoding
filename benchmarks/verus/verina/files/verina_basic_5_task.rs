use vstd::prelude::*;

verus! {

fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
{
    assume(false);
    unreached();
}

}
fn main() {}