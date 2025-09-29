// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn gt_asym(a: int, b: int)
    ensures
        a > b ==> !(b > a),
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_greater(x1: &Vec<i8>, x2: &Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == (x1[i] as int > x2[i] as int)) &&
            (result[i] == true ==> !(x2[i] as int > x1[i] as int)) &&
            (result[i] == true || result[i] == false)
// </vc-spec>
// <vc-code>
{
    let n = x1.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            res.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i as int ==> res@[j] == (x1[j] as int > x2[j] as int),
        decreases (n as int) - (i as int)
    {
        let xi = x1[i];
        let xj = x2[i];
        let b: bool = xi > xj;
        if b {
            proof { gt_asym(xi as int, xj as int); }
        }
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}