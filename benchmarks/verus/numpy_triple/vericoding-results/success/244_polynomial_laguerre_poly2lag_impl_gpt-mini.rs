// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn _helper_noop() {
}

// </vc-helpers>

// <vc-spec>
fn poly2lag(pol: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == pol.len(),

        true,
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < pol.len()
        invariant
            i <= pol.len(),
            res.len() == i,
        decreases pol.len() - i
    {
        res.push(0i8);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}