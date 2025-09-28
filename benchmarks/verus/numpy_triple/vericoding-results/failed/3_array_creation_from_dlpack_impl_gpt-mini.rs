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
/* helper modified by LLM (iteration 5): added Clone bound to allow cloning vectors */
pub fn vec_clone_preserves<T>(v: &Vec<T>) -> (r: Vec<T>) where T: std::clone::Clone
    ensures
        r.len() == v.len(),
        forall|i: int| 0 <= i < r.len() ==> r[i] == v[i],
{
    let r = v.clone();
    r
}

/* helper modified by LLM (iteration 5): basic property of vec clone */
pub proof fn vec_clone_basic_properties<T>(v: &Vec<T>) where T: std::clone::Clone
    ensures
        v.clone().len() == v.len(),
{
    proof {
        assert(v.clone().len() == v.len());
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
    /* code modified by LLM (iteration 5): implement cloning behavior using helper that preserves contents */
    let result: Vec<T>;
    if copy == Some(true) {
        // produce a copied Vec of the underlying data
        result = vec_clone_preserves(&x.data);
    } else if copy == Some(false) {
        // when copy == false, we still return the same contents; ownership/aliasing
        // semantics are approximated by returning a clone here (runtime ownership constraints)
        result = vec_clone_preserves(&x.data);
    } else {
        // default: return a clone
        result = vec_clone_preserves(&x.data);
    }
    proof {
        assert(result.len() == x.data.len());
        assert(forall|i: int| 0 <= i < result.len() ==> result[i] == x.data[i]);
    }
    result
}

// </vc-code>

}
fn main() {}