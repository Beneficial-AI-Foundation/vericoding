// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix type casts from nat to int for Seq::len and subrange bounds */
spec fn remove_kth_seq<T>(s: Seq<T>, k: int) -> Seq<T>
    recommends
        0 < k && k < s.len() as int
{
    s.subrange(0, k - 1).add(s.subrange(k, s.len() as int))
}
// </vc-helpers>

// <vc-spec>
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)

    requires
        list.len() > 0,
        0 < k < list@.len(),

    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use clone + remove with proper int/nat casts in proofs */
    proof { assert(0 < k); }
    let mut new_list = list.clone();
    let idx: usize = k - 1;

    proof {
        assert((list.len() as int) == (list@.len() as int));
        assert(new_list@ == list@);
        assert((new_list.len() as int) == (new_list@.len() as int));
        assert(0 < k);
        assert((k as int) < (list@.len() as int));
        assert(((k as int) - 1) < (list@.len() as int));
        assert((idx as int) == ((k as int) - 1));
        assert((idx as int) < (new_list.len() as int));
    }
    assert(idx < new_list.len());

    new_list.remove(idx);
    new_list
}
// </vc-code>

}
fn main() {}