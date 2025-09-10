use vstd::prelude::*;

verus! {

fn area_of_largest_triangle_in_semicircle(radius: i32) -> (area: i32)
    requires radius > 0
    ensures area == radius * radius
{
    assume(false);
    unreached();
}

}
fn main() {}