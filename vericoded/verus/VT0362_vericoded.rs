// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn i8_one_positive()
    ensures
        1i8 as int > 0,
{}

// </vc-helpers>

// <vc-spec>
fn spacing(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] result@[i] as int > 0
// </vc-spec>
// <vc-code>
{
    let mut y: Vec<i8> = Vec::new();
    while y.len() < x.len()
        invariant
            y@.len() <= x@.len(),
            forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] as int > 0,
        decreases x.len() - y.len()
    {
        y.push(1i8);
    }
    y
}
// </vc-code>


}
fn main() {}