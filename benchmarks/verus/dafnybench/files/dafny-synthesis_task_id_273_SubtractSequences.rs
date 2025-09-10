use vstd::prelude::*;

verus! {

fn subtract_sequences(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i],
{
    assume(false);
    unreached()
}

}
fn main() {}