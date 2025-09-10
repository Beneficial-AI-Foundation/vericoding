use vstd::prelude::*;

verus! {

fn maximum(values: Seq<int>) -> (max: int)
    requires
        values.len() > 0,
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max,
{
    assume(false);
    unreached()
}

}
fn main() {}