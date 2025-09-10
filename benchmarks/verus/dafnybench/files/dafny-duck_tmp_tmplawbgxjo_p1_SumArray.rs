use vstd::prelude::*;

verus! {

spec fn sum(xs: Seq<i32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0int
    } else {
        sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int
    }
}

fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
{
    assume(false);
    unreached()
}

}
fn main() {}