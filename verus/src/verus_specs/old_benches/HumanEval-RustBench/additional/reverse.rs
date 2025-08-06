use vstd::prelude::*;

verus! {

fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}
}
