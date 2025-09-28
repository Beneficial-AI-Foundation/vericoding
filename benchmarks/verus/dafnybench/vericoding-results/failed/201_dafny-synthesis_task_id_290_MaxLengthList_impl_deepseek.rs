use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn max_length_exists(lists: Seq<Seq<int>>, n: nat)
    requires 
        n > 0,
        lists.len() == n,
        forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= 0
    ensures 
        false
{
}

spec fn max_list_spec(lists: Seq<Seq<int>>) -> (max_index: int, max_len: nat)
    recommends lists.len() > 0
    ensures 
        0 <= max_index < lists.len(),
        max_len == lists[max_index].len(),
        forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_len
{
    if lists.len() == 1 {
        (0, lists[0].len())
    } else {
        let (prev_index, prev_max) = max_list_spec(lists.drop_last());
        let last_len = lists[lists.len() - 1].len();
        if last_len > prev_max {
            (lists.len() - 1, last_len)
        } else {
            (prev_index, prev_max)
        }
    }
}

proof fn max_list_spec_correct(lists: Seq<Seq<int>>)
    requires lists.len() > 0
    ensures 
        let (max_index, max_len) = max_list_spec(lists);
        0 <= max_index < lists.len(),
        max_len == lists[max_index].len(),
        forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_len
{
    if lists.len() == 1 {
        assert forall|i: int| 0 <= i < lists.len() implies lists[i].len() <= lists[0].len() by {
            assert(i == 0);
        };
    } else {
        let sub = lists.drop_last();
        assert(sub.len() > 0) by { reveal_with_fuel(Seq::drop_last, 2); };
        max_list_spec_correct(sub);
        let (prev_index, prev_max) = max_list_spec(sub);
        let last_len = lists[lists.len() - 1].len();
        if last_len > prev_max {
            assert forall|i: int| 0 <= i < lists.len() implies lists[i].len() <= last_len by {
                if i < lists.len() - 1 {
                    assert(lists[i].len() == sub[i].len());
                    assert(sub[i].len() <= prev_max);
                    assert(prev_max < last_len);
                } else {
                    assert(i == lists.len() - 1);
                }
            };
        } else {
            assert forall|i: int| 0 <= i < lists.len() implies lists[i].len() <= prev_max by {
                if i < lists.len() - 1 {
                    assert(lists[i].len() == sub[i].len());
                } else {
                    assert(i == lists.len() - 1);
                    assert(lists[i].len() == last_len);
                    assert(last_len <= prev_max);
                }
            };
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    let mut max_index = 0;
    let mut max_len = lists[0].len();
    let mut i: usize = 1;
    while i < lists.len()
        invariant
            0 <= max_index < lists.len(),
            max_len == lists[max_index].len(),
            forall|j: int| 0 <= j < i ==> lists[j].len() <= max_len,
            i <= lists.len()
    {
        let current_len = lists[i].len();
        if current_len > max_len {
            max_index = i;
            max_len = current_len;
        }
        i += 1;
    }
    proof {
        assert forall|j: int| 0 <= j < lists.len() implies lists[j].len() <= max_len by {
            if j < i as int {
                // Already covered by invariant
            } else {
                assert(j >= i as int && j < lists.len() as int);
                let k: usize = j as usize;
                assert(k >= i && k < lists.len());
                // This case should not occur since i == lists.len() after loop
                assert(false);
            }
        };
    }
    lists[max_index].clone()
}
// </vc-code>

fn main() {}

}