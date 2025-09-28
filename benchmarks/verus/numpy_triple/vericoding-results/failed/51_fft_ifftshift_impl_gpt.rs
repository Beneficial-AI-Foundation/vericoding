// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ifftshift(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result[i] == x[((i + (x@.len() as int) / 2) % (x@.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    let n: int = x.len() as int;
    let k: int = n / 2;
    let mut res: Vec<f32> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            x.len() as int == n,
            n > 0,
            k == n / 2,
            0 <= i <= n,
            res.len() as int == i,
            forall|j: int| 0 <= j < i ==> res[j] == x[((j + k) % n) as int],
        decreases n - i
    {
        let idx: int = (i + k) % n;
        assert(0 <= idx && idx < n);
        let val = x[idx as int];
        res.push(val);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}