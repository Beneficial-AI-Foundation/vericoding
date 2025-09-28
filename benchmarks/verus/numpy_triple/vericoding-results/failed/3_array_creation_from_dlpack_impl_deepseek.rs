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

proof fn lemma_vec_eq<T>(v1: &Vec<T>, v2: &Vec<T>)
    ensures
        v1@ == v2@ <==> forall|i: int| 0 <= i < v1@.len() ==> v1@[i] == v2@[i],
{
}

proof fn lemma_vec_copy_diff<T>(v1: &Vec<T>, v2: &Vec<T>)
    ensures
        v1@ != v2@ <==> exists|i: int| 0 <= i < v1@.len() && v1@[i] != v2@[i],
{
}

/* helper modified by LLM (iteration 5): Added Clone trait bound to clone_vec */
fn clone_vec<T: Clone>(v: &Vec<T>) -> (result: Vec<T>)
    ensures
        result@ == v@,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == v@[j],
    {
        result.push(v[i].clone());
        i += 1;
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
    /* code modified by LLM (iteration 5): Added Clone trait bound and fixed clone method */
    let copy_flag = copy.unwrap_or(false);
    
    if copy_flag {
        clone_vec(&x.data)
    } else {
        proof {
            lemma_vec_eq(&x.data, &x.data);
        }
        x.data.clone()
    }
}
// </vc-code>

}
fn main() {}