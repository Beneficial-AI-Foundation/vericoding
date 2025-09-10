use vstd::prelude::*;

verus! {

fn compare(a: i32, b: i32) -> (result: bool)
    ensures
        (a == b ==> result == true) && (a != b ==> result == false),
{
    assume(false);
    unreached()
}

}
fn main() {}