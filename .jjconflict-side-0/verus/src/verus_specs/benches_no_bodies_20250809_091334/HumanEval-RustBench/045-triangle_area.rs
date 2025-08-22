use vstd::prelude::*;

verus! {

fn triangle_area(a: u64, h: u64) -> (area: u64)
    // pre-conditions-start
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,
    // pre-conditions-end
    // post-conditions-start
    ensures
        area == a * h / 2,
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
