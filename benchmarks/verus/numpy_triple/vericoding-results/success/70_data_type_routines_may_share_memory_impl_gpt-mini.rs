// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn always_false() -> bool {
    false
}
// </vc-helpers>

// <vc-spec>
fn may_share_memory(a: &Vec<i8>, b: &Vec<i8>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (result == true ==> true) &&

        true &&

        true
// </vc-spec>
// <vc-code>
{
    let result = always_false();
    result
}
// </vc-code>

}
fn main() {}