// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn reversed(arr: Seq<char>, outarr: Seq<char>) -> bool {
    arr.len() == outarr.len() &&
    forall|k: int| 0 <= k < arr.len() ==> outarr[k] == arr[arr.len() - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed lemma for set-based approach as it is unused by the new push-based implementation. */
// </vc-helpers>

// <vc-spec>
fn yarra(arr: &Vec<char>) -> (outarr: Vec<char>)
    requires arr.len() > 0
    ensures outarr.len() == arr.len() && reversed(arr@, outarr@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by using a push-based loop instead of Vec::from_elem */
    let len = arr.len();
    let mut outarr = Vec::new();
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i <= len,
            arr.len() == len,
            outarr.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> outarr@[k] == arr@[(len as int) - 1 - k],
        decreases len - i
    {
        outarr.push(arr[len - 1 - i]);
        i = i + 1;
    }

    outarr
}
// </vc-code>

}
fn main() {}