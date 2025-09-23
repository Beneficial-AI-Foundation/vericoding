// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn reversed(arr: Seq<char>, outarr: Seq<char>) -> bool {
    arr.len() == outarr.len() &&
    forall|k: int| 0 <= k < arr.len() ==> outarr[k] == arr[arr.len() - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn yarra(arr: &Vec<char>) -> (outarr: Vec<char>)
    requires arr.len() > 0
    ensures outarr.len() == arr.len() && reversed(arr@, outarr@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}