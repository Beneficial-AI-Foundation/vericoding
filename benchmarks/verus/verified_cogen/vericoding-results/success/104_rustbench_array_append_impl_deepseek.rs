// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn array_append_helper(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
{
    let mut result = a.clone();
    result.push(b);
    result
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
// </vc-spec>
// <vc-code>
{
    let mut result = a.clone();
    result.push(b);
    result
}
// </vc-code>

}
fn main() {}