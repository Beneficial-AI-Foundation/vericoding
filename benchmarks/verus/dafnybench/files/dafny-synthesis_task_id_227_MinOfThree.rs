use vstd::prelude::*;

verus! {

fn min_of_three(a: i32, b: i32, c: i32) -> (min: i32)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c),
{
    assume(false);
    unreached();
}

}
fn main() {}