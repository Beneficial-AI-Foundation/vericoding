// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn len_matches_size(a: &Vec<f64>) -> bool { true }
// </vc-helpers>

// <vc-spec>
fn size(a: &Vec<f64>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
{
    a.len()
}
// </vc-code>

}
fn main() {}