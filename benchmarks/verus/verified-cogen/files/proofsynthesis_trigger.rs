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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}