// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn shape<T>(a: &Vec<T>) -> (result: usize)
    ensures result == a.len()
// </vc-spec>
// <vc-code>
{
    let result = a.len();
    result
}
// </vc-code>

}
fn main() {}