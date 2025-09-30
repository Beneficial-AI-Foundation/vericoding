// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ndim<T>(a: &Vec<T>) -> (result: usize)
    ensures result == 1
// </vc-spec>
// <vc-code>
{
    1usize
}
// </vc-code>

}
fn main() {}