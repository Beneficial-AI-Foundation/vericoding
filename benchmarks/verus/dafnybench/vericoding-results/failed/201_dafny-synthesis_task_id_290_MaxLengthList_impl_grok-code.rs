use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    let mut max_list: Vec<int> = lists[0].clone();
    proof {
        let mut max_seq: Ghost<Seq<int>> = Ghost(max_list@);
    }
    let mut i: usize = 1;
    while i < lists.len()
        invariant
            0 <= i <= lists@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] (lists@[j].len()) <= (*max_seq).len(),
            exists|k: int| 0 <= k < i && #[trigger] (lists@[k]) == (*max_seq)
        decreases
            (lists.len() as int - i as int)
    {
        if lists[i].len() > max_list.len() {
            max_list = lists[i].clone();
            proof {
                max_seq = Ghost(lists@[i]);
            }
        }
        i = i + 1;
    }
    proof {
        assert(max_list@ == *max_seq);
    }
    max_list
}
// </vc-code>

fn main() {}

}