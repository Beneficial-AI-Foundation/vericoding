// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus!{

spec fn f(seq: Seq<u64>, i: int) -> (result: bool) {
    seq[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>
proof fn property_holds_for_index(arr: Seq<u64>, i: int)
    requires
        forall |j: int| f(arr, j),
    ensures
        f(arr, i)
{}
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
    proof {
        property_holds_for_index(arr@, i as int);
    }
    let ret = arr[i];
    ret
}
// </vc-code>

}
fn main() {}