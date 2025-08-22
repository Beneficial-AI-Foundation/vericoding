use vstd::prelude::*;

verus! {

fn cal_div() -> (r: (u32, u32))
    ensures
        r.0 == 27,
        r.1 == 2,
{
    (27, 2)
}

} // verus!
fn main() {}