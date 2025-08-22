use vstd::prelude::*;

verus! {

fn mod_arrays(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] % b[i],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}

}