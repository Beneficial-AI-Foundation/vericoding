use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}
}
