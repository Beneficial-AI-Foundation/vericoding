// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_in_bounds(len: int, i: int) -> bool { 0 <= i && i < len }
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn r_(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        forall|j: int| 0 <= j < b.len() ==> result[a.len() + j] == b[j]
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|k: int| 0 <= k < i as int ==> res[k] == a[k]
        decreases (a.len() - i) as int
    {
        let x = a[i];
        res.push(x);
        i += 1;
    }

    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            res.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() as int ==> res[k] == a[k],
            forall|k: int| 0 <= k < j as int ==> res[a.len() as int + k] == b[k]
        decreases (b.len() - j) as int
    {
        let y = b[j];
        res.push(y);
        j += 1;
    }
    res
}
// </vc-code>

}
fn main() {}