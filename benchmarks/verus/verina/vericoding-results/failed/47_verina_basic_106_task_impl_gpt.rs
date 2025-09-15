// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res[j] == a[j] + b[j],
        decreases n - i
    {
        let s = a[i] + b[i];
        res.push(s);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}