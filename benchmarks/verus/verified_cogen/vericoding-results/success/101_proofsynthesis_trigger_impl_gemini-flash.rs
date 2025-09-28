// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus!{

spec fn f(seq: Seq<u64>, i: int) -> (result: bool) {
    seq[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unused helper */
// </vc-helpers>

// <vc-spec>
fn get_element_check_property(arr: Vec<u64>, i: usize) -> (ret: u64)

    requires
        arr.len() > 0,
        0 < i < arr@.len(),
        forall |i: int| f(arr@, i),

    ensures
        ret == i + 2,
        ret == arr@[i as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation error by removing unused `i_int` variable and passing `i` directly. Added assertions to help with verification. */
{
    assert(f(arr@, i as int));
    let ret = arr[i];
    assert(ret == i as int + 2);
    ret
}
// </vc-code>

}
fn main() {}