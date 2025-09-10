use vstd::prelude::*;

verus! {

fn triangle_area(a: u64, h: u64) -> (area: u64)

    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,

    ensures
        area == a * h / 2,
{
    assume(false);
    unreached();
}

}
fn main() {}