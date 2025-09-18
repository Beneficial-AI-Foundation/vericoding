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
/* helper modified by LLM (iteration 5): vector sequence equality predicate */
spec fn vec_seq_eq<T>(a: &Vec<T>, b: &Vec<T>) -> bool { a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> a[i] == b[i] }

/* helper modified by LLM (iteration 5): proof that cloning preserves sequence */
proof fn clone_preserves_seq<T: std::clone::Clone>(v: &Vec<T>) ensures vec_seq_eq(v, &v.clone()) {
    proof {
        assert(v.len() == v.clone().len());
        assert(forall|i: int| 0 <= i < v.len() ==> v[i] == v.clone()[i]);
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
    /* code modified by LLM (iteration 5): clone the underlying data into a new Vec and return it */
    let result: Vec<T> = x.data.clone();
    result
}
// </vc-code>

}
fn main() {}