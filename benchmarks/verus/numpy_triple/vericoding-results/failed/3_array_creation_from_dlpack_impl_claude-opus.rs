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
    /* code modified by LLM (iteration 2): Fixed compilation error by building vector element by element without clone */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.data.len()
        invariant
            i <= x.data.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x.data[j],
    {
        result.push(x.data[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}