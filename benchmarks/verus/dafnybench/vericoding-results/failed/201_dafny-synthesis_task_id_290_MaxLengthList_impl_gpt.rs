use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    let n = lists.len();
    let mut best_idx: usize = 0;
    let mut i: usize = 1;
    while i < n
        invariant n == lists.len()
        invariant n > 0
        invariant 1 <= i && i <= n
        invariant best_idx < n
        invariant forall|j: int| 0 <= j && j < i as int ==> lists[j as usize].len() <= lists[best_idx].len()
    {
        let li = lists[i].len();
        let lb = lists[best_idx].len();
        if li >= lb {
            best_idx = i;
        }
        i = i + 1;
    }
    let res = lists[best_idx].clone();
    proof {
        assert(i == n);
        assert(res.len() == lists[best_idx].len());
        assert(res@ == lists[best_idx]@);
        assert(0 <= best_idx as int && (best_idx as int) < n as int);
        assert(exists|k:int| 0 <= k && k < n as int && res@ == lists[k as usize]@);
    }
    res
}
// </vc-code>

fn main() {}

}