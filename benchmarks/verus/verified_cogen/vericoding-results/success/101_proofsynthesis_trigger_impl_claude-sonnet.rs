// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus!{

spec fn f(seq: Seq<u64>, i: int) -> (result: bool) {
    seq[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 2): added proof block to establish postcondition */
    proof {
        assert(f(arr@, i as int));
        assert(arr@[i as int] == i as int + 2);
    }
    arr[i]
}
// </vc-code>

}
fn main() {}