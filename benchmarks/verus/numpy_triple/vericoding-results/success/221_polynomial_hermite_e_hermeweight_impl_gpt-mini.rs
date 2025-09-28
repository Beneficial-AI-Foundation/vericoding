// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_clone_preserve_len<T: Copy>(v: Vec<T>) -> (v2: Vec<T>)
    ensures
        v2.len() == v.len(),
{
    let v2 = v.clone();
    v2
}
// </vc-helpers>

// <vc-spec>
fn hermeweight(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let result = x.clone();
    result
}
// </vc-code>


}
fn main() {}