// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


// </vc-helpers>

// <vc-spec>
fn numpy_logical_xor(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    let n: usize = x1.len();
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n as int,
            x2.len() == n as int,
            0 <= i as int,
            i as int <= n as int,
            r.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> r[j] == (x1[j] != x2[j]),
        decreases n as int - i as int
    {
        let b1 = x1[i];
        let b2 = x2[i];
        let val = b1 != b2;
        r.push(val);
        proof {
            assert(r[i as int] == val);
        }
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}