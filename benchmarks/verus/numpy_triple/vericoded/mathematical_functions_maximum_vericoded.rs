// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_i8(a: i8, b: i8) -> (r: i8)
    ensures
        r == if a >= b { a } else { b },
        r >= a && r >= b,
        r == a || r == b,
{
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn maximum(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] == if x1@[i] >= x2@[i] { x1@[i] } else { x2@[i] },
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] >= x1@[i] && result@[i] >= x2@[i],
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] == x1@[i] || result@[i] == x2@[i],
// </vc-spec>
// <vc-code>
{
    let n = x1.len();
    let mut r: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i as int ==> r@[j] == if x1@[j] >= x2@[j] { x1@[j] } else { x2@[j] },
            forall|j: int| 0 <= j < i as int ==> r@[j] >= x1@[j] && r@[j] >= x2@[j],
            forall|j: int| 0 <= j < i as int ==> r@[j] == x1@[j] || r@[j] == x2@[j],
        decreases n - i
    {
        let a = x1[i];
        let b = x2[i];
        assert(a == x1@[i as int]);
        assert(b == x2@[i as int]);
        let m = max_i8(a, b);
        r.push(m);
        i = i + 1;
    }
    r
}
// </vc-code>


}
fn main() {}