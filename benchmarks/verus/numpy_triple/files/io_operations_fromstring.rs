use vstd::prelude::*;

verus! {

fn fromstring(input: &str, sep: &str, n: usize) -> (result: Vec<f64>)
    requires n > 0,
    ensures 
        result.len() <= n,
        forall|i: int| 0 <= i < result.len() ==> true,
{
    assume(false);
    unreached()
}

}
fn main() {}