#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus!{
spec fn f(seq: Seq<u64>, i: int) -> bool {
    seq[i] == i + 2
}

fn get_element_check_property(arr: Vec<u64>, i: usize) -> (ret: u64)
    requires
        arr.len() > 0,
        0 < i < arr@.len(),
        forall |i: int| f(arr@, i),
    ensures
        ret == i + 2,
        ret == arr@[i as int],
{
    /* code modified by LLM (iteration 1): Added assertion to instantiate the universal quantifier for the specific index i, proving that arr[i] == i + 2 */
    assert(f(arr@, i as int));
    arr[i]
}
}