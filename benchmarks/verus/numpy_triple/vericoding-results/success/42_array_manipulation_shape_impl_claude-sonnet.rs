// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn shape<T>(a: &Vec<T>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
{
    a.len()
}
// </vc-code>

}
fn main() {}