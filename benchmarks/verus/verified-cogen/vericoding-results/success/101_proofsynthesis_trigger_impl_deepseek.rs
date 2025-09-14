// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus!{

spec fn f(seq: Seq<u64>, i: int) -> (result: bool) {
    seq[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>

spec fn is_in_range(seq: Seq<u64>, i: int) -> bool {
    0 <= i < seq.len()
}

proof fn element_lemma(seq: Seq<u64>, i: int)
    requires
        f(seq, i),
        is_in_range(seq, i),
    ensures
        seq[i] == i + 2
{
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
    proof {
        element_lemma(arr@, i as int);
    }
    let result = arr[i];
    result
}
// </vc-code>

}
fn main() {}