// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus!{

spec fn f(seq: Seq<u64>, i: int) -> (result: bool) {
    seq[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_arr_index_property(seq: Seq<u64>, i: int)
    requires
        0 <= i < seq.len(),
        forall |j: int| f(seq, j),
    ensures
        seq[i] == i + 2
{
    reveal(f);
    assert(f(seq, i));
}
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
    let ret_val = arr[i];
    proof {
        lemma_arr_index_property(arr@, i as int);
    }
    ret_val
}
// </vc-code>

}
fn main() {}