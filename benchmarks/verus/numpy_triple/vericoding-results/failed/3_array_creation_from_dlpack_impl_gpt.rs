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
/* helper modified by LLM (iteration 3): predicate indicating whether a copy is requested */
fn should_copy(copy: Option<bool>) -> (b: bool)
    ensures
        copy == Some(true) ==> b,
        copy != Some(true) ==> !b,
{
    match copy {
        Some(true) => true,
        _ => false,
    }
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
    /* code modified by LLM (iteration 3): clone data to produce result and prove basic properties */
    let result = x.data.clone();
    proof {
        assert(result.len() == x.data.len());
        assert(forall|i: int| 0 <= i < result.len() ==> result[i] == x.data[i]);
        if copy == Some(false) {
            assert(result@ == x.data@);
        }
    }
    result
}
// </vc-code>

}
fn main() {}