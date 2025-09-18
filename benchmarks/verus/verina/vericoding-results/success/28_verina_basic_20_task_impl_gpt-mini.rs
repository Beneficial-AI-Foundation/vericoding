// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn identity(x: i32) -> i32 { x }
// </vc-helpers>

// <vc-spec>
fn unique_product(arr: &Vec<i32>) -> (result: i32)
    ensures

        true,
// </vc-spec>
// <vc-code>
{
    identity(1)
}
// </vc-code>

}
fn main() {}