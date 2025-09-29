// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn less_equal(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1@.len() ==> result@[i] == (x1@[i] <= x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (result@[i] == true <==> x1@[i] <= x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (result@[i] == false <==> x1@[i] > x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (x1@[i] == x2@[i] ==> result@[i] == true),
// </vc-spec>
// <vc-code>
{
    let n = x1.len();
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            r@.len() == i as int,
            i <= n,
            forall|k: int| 0 <= k < i as int ==> r@[k] == (x1@[k] <= x2@[k]),
        decreases n - i
    {
        let b = x1[i] <= x2[i];
        r.push(b);
        i = i + 1;
    }
    r
}
// </vc-code>


}
fn main() {}