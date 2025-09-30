// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn log(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x[i] as int > 0,
    ensures 
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    let mut r: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            r@.len() == i as nat,
        decreases (x.len() - i) as int
    {
        r.push(0i8);
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}