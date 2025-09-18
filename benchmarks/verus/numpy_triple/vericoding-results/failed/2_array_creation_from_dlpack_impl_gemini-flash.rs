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
/* helper modified by LLM (iteration 5): Removed helpers as they are no longer needed. */
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
/* code modified by LLM (iteration 5): Added missing Clone bound to the type parameter T. */
{
    if copy == Some(true) {
        let mut new_vec: Vec<T> = Vec::new();
        let mut i = 0;
        while i < x.data.len()
            invariant
                i <= x.data.len(),
                new_vec.len() == i,
                forall|j: int| 0 <= j < i ==> new_vec[j] == x.data[j]
        {
            new_vec.push(x.data[i].clone());
            i = i + 1;
        }
        new_vec
    } else {
        let mut result_vec = Vec::new();
        let mut i = 0;
        while i < x.data.len()
            invariant
                i <= x.data.len(),
                result_vec.len() == i,
                forall|j: int| 0 <= j < i ==> result_vec[j] == x.data[j]
        {
            result_vec.push(x.data[i].clone());
            i = i + 1;
        }
        result_vec
    }
}
// </vc-code>

}
fn main() {}