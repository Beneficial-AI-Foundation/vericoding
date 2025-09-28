// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct DLPackObject<T> {
    pub data: Vec<T>,
    pub has_dlpack: bool,
    pub has_dlpack_device: bool,
    pub device: String,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change, helper is correct */
fn clone_vec<T: Clone>(v: &Vec<T>) -> (result: Vec<T>)
    ensures result@ == v@
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            result.len() == i as nat,
            forall|j: int| 0 <= j < (i as nat) ==> result@[j] == v@[j],
        decreases v.len() - i
    {
        result.push(v[i].clone());
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn from_dlpack<T>(x: &DLPackObject<T>, device: Option<&str>, copy: Option<bool>) -> (result: Vec<T>)
    requires 
        x.has_dlpack && x.has_dlpack_device,
        device.is_none() || device == Some("cpu"),
    ensures
        result.len() == x.data.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x.data[i],
        copy == Some(true) ==> result@ != x.data@,
        copy == Some(false) ==> result@ == x.data@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper function to fix compilation errors */
    // The spec is contradictory for the case `copy == Some(true)`,
    // ensuring both `result@ == x.data@` (via the forall) and `result@ != x.data@`.
    // This implementation satisfies all non-contradictory ensures clauses.
    // It will fail verification on the contradictory clause.
    // A `T: Clone` trait bound on `from_dlpack` is required for this to compile.
    let result = clone_vec(&x.data);
    result
}
// </vc-code>

}
fn main() {}