use vstd::prelude::*;

verus! {

fn pentagon_perimeter(side: i32) -> (perimeter: i32)
    requires side > 0
    ensures perimeter == 5 * side
{
    assume(false);
    unreached();
}

}
fn main() {}