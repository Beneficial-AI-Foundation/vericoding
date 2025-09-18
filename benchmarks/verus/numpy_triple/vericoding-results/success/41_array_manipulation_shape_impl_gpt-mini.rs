// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn len_identity<T>(a: &Vec<T>) ensures a.len() == a.len() { }
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