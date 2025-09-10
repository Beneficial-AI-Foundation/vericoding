use vstd::prelude::*;

verus! {

fn NPY_LOG2E() -> (result: f64)
    ensures
        result == 1.442695040888963407359924681001892137,
{
    assume(false);
    unreached();
}

}
fn main() {}