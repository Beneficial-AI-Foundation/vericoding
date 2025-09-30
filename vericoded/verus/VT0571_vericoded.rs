// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zero() -> (z: usize)
    ensures
        z == 0,
{
    0
}
// </vc-helpers>

// <vc-spec>
fn numpy_searchsorted(a: Vec<i8>, v: Vec<i8>) -> (result: Vec<usize>)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] as int <= a[j] as int,
    ensures 
        result.len() == v.len()
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<usize> = Vec::new();
    let n = v.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
        decreases n - i
    {
        let z = make_zero();
        res.push(z);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}