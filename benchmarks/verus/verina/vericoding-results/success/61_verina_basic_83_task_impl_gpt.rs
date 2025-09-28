// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn id_i(x: int) -> int { x }
// </vc-helpers>

// <vc-spec>
fn concat(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> result[k + a.len()] == b[k],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            (i as int) <= a.len(),
            result.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result[k] == a[k],
        decreases a.len() - (i as int)
    {
        result.push(a[i]);
        i = i + 1;
    }
    let mut j: usize = 0;
    while j < b.len()
        invariant
            0 <= j as int,
            (j as int) <= b.len(),
            result.len() == a.len() + j as int,
            forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k < j as int ==> result[k + a.len()] == b[k],
        decreases b.len() - (j as int)
    {
        result.push(b[j]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}