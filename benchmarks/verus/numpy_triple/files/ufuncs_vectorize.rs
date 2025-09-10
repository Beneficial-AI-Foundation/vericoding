use vstd::prelude::*;

verus! {

fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
{
    assume(false);
    unreached()
}

}
fn main() {}