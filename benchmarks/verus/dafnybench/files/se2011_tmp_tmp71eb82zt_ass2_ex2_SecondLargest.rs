use vstd::prelude::*;

verus! {

fn second_largest(a: &[i32]) -> (seclar: i32)
    requires a.len() > 0
{
    assume(false);
    unreached()
}

}
fn main() {}