#[allow(unused_imports)]
use vstd::prelude::*;


verus!{

spec fn f(seq: Seq<u64>, i: int) -> (result: bool) {
    seq[i] == i + 2
}
// pure-end

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_element_check_property(arr: Vec<u64>, i: usize) -> (ret: u64)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 < i < arr@.len(),
        forall |i: int| f(arr@, i),
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret == i + 2,
        ret == arr@[i as int],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    proof {
        assert(f(arr@, i as int));
        assert(arr@[i as int] == (i as int) + 2);
    }
    arr[i]
}
// </vc-code>

}

fn main() {}