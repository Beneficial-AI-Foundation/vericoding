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
    let n: usize = lists.len();
    let mut min_idx: usize = 0;
    let mut min_len: usize = lists[0].len();
    let mut k: usize = 1;
    while k < n
        invariant k <= n;
        invariant min_idx < n;
        invariant min_len == lists[min_idx].len();
        invariant forall|j: usize| j < k ==> min_len <= lists[j].len();
    {
        let cur_len = lists[k].len();
        if cur_len < min_len {
            min_idx = k;
            min_len = cur_len;
        }
        k += 1;
    }

    let res: usize = min_len;
    proof {
        // witness for existence
        assert(min_idx < lists.len());
        assert(res == lists[min_idx].len());

        // at loop exit k == n
        assert(k == n);

        // provide existence witness and assert
        let wi: int = min_idx as int;
        assert(0 <= wi && wi < lists.len() as int);
        assert(res == lists[wi as usize].len());
        assert(exists|i: int| 0 <= i && i < lists.len() as int && res == lists[i as usize].len());

        // prove minimality for all indices (convert int -> usize inside)
        forall|i: int| #![trigger] 0 <= i && i < lists.len() as int ==>
        {
            let ui: usize = i as usize;
            // since k == n and ui < lists.len() == n, we have ui < k
            assert(ui < k);
            // use loop invariant to get min_len <= lists[ui].len()
            assert(min_len <= lists[ui].len());
            assert(res <= lists[ui].len());
        }
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}