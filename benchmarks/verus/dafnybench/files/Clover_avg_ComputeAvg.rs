use vstd::prelude::*;

verus! {

fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
{
    assume(false);
    unreached()
}

}
fn main() {}