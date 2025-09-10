use vstd::prelude::*;

verus! {

fn max_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
{
    assume(false);
    unreached();
}

}
fn main() {}