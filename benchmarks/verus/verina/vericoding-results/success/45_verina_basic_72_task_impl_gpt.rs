// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_i32(x: i32) -> i32 { x }
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        result[a.len() as int] == b,
// </vc-spec>
// <vc-code>
{
    let mut r = a.clone();
    r.push(b);
    r
}
// </vc-code>

}
fn main() {}