use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    // pre-conditions-start
    requires
        lists.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        exists|i: int| #![auto] 0 <= i < lists.len() && result == lists[i].len(),
        forall|i: int| #![auto] 0 <= i < lists.len() ==> result <= lists[i].len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut min_idx: usize = 0;
    let mut min_len: usize = lists[0].len();
    let mut i: usize = 1;
    while i < lists.len() 
        invariant i <= lists.len();
        invariant min_idx < lists.len();
        invariant min_len == lists[min_idx].len();
        invariant forall|j: int| 0 <= j && j < (i as int) ==> min_len <= lists[j as usize].len();
    {
        let cur_len: usize = lists[i].len();
        if cur_len < min_len {
            min_len = cur_len;
            min_idx = i;
        }
        i += 1;
    }

    proof {
        // witness for existence: min_idx as int
        assert(min_idx < lists.len());
        assert(min_len == lists[min_idx].len());
        assert(0 <= (min_idx as int));
        assert((min_idx as int) < (lists.len() as int));
        assert(min_len == lists[(min_idx as usize)].len());
        // show existence required by the spec
        assert(exists|k: int| 0 <= k && k < lists.len() as int && min_len == lists[k as usize].len());
        // and minimality (forall) follows from the loop invariant with i == lists.len()
        assert(forall|j: int| 0 <= j && j < lists.len() as int ==> min_len <= lists[j as usize].len());
    }

    min_len
    // impl-end
}
// </vc-code>

fn main() {}
}