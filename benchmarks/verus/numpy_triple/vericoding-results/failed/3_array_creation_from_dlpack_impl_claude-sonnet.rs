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
/* helper modified by LLM (iteration 5): Manual vector cloning using Clone trait */
fn manual_clone<T: Clone>(source: &Vec<T>) -> (result: Vec<T>)
    ensures
        result.len() == source.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == source[i],
{
    let mut cloned = Vec::new();
    let mut i = 0;
    while i < source.len()
        invariant
            i <= source.len(),
            cloned.len() == i,
            forall|j: int| 0 <= j < i ==> cloned[j] == source[j],
    {
        cloned.push(source[i].clone());
        i += 1;
    }
    cloned
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
    /* code modified by LLM (iteration 5): Use Clone trait bound and fix compilation errors */
    match copy {
        Some(true) => {
            let mut new_data = Vec::new();
            let mut i = 0;
            while i < x.data.len()
                invariant
                    i <= x.data.len(),
                    new_data.len() == i,
                    forall|j: int| 0 <= j < i ==> new_data[j] == x.data[j],
            {
                new_data.push(x.data[i].clone());
                i += 1;
            }
            new_data
        },
        Some(false) => {
            let mut result = Vec::new();
            let mut i = 0;
            while i < x.data.len()
                invariant
                    i <= x.data.len(),
                    result.len() == i,
                    forall|j: int| 0 <= j < i ==> result[j] == x.data[j],
            {
                result.push(x.data[i].clone());
                i += 1;
            }
            result
        },
        None => {
            let mut result = Vec::new();
            let mut i = 0;
            while i < x.data.len()
                invariant
                    i <= x.data.len(),
                    result.len() == i,
                    forall|j: int| 0 <= j < i ==> result[j] == x.data[j],
            {
                result.push(x.data[i].clone());
                i += 1;
            }
            result
        }
    }
}
// </vc-code>

}
fn main() {}