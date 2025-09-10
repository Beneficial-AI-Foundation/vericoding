use vstd::prelude::*;

verus! {

fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
{
    assume(false);
    unreached()
}

}
fn main() {}