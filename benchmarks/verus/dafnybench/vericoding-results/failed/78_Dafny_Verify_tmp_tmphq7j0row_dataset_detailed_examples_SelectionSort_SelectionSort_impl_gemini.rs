// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted_prefix(s: Seq<i32>, k: nat) -> bool {
    forall|i: int, j: int| 0 <= i < j < k ==> s[i] <= s[j]
}

spec fn partitioned(s: Seq<i32>, i: nat) -> bool {
    forall|k1: int, k2: int| 0 <= k1 < i <= k2 < s.len() ==> s[k1] <= s[k2]
}

fn find_min_index(a: &Vec<i32>, start: usize) -> (min_idx: usize)
    requires
        start < a.len(),
    ensures
        start <= min_idx < a.len(),
        forall|k: int| start as int <= k < a.len() as int ==> a@[min_idx as int] <= a@[k],
{
    let mut min_idx = start;
    let mut i = start + 1;
    while i < a.len()
        invariant
            start <= i <= a.len(),
            start <= min_idx < i,
            forall|k: int| start as int <= k < i as int ==> a@[min_idx as int] <= a@[k],
        decreases a.len() - i
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}

/* helper modified by LLM (iteration 5): added proof for selection step lemma */
proof fn selection_step_preserves_invs(s: Seq<i32>, i: nat, min_idx: nat)
    requires
        i < s.len(),
        i <= min_idx < s.len(),
        sorted_prefix(s, i),
        partitioned(s, i),
        forall|k: int| i as int <= k < s.len() ==> s[min_idx] <= s[k],
    ensures
        sorted_prefix(s.swap(i as int, min_idx as int), (i + 1) as nat),
        partitioned(s.swap(i as int, min_idx as int), (i + 1) as nat),
{
    let s_after = s.swap(i as int, min_idx as int);
    let i_int = i as int;
    let min_idx_int = min_idx as int;
    vstd::seq::lemma_swap_properties(s, i_int, min_idx_int);

    assert forall|k1: int, k2: int| 0 <= k1 < k2 < (i + 1) as int implies s_after[k1] <= s_after[k2] {
        if k2 < i_int {
        } else { 
            assert(k2 == i_int);
            assert(s_after[k1] == s[k1]);
            assert(s_after[i_int] == s[min_idx_int]);
            assert(partitioned(s, i));
            assert(s[k1] <= s[min_idx_int]);
        }
    }

    assert forall|k1: int, k2: int| 0 <= k1 < (i + 1) as int && (i + 1) as int <= k2 < s.len() implies s_after[k1] <= s_after[k2] {
        if k1 < i_int {
            assert(s_after[k1] == s[k1]);
            assert(partitioned(s, i));
            if k2 == min_idx_int {
                assert(s_after[k2] == s[i_int]);
                assert(s[k1] <= s[i_int]);
            } else {
                assert(s_after[k2] == s[k2]);
                assert(s[k1] <= s[k2]);
            }
        } else { 
            assert(k1 == i_int);
            assert(s_after[k1] == s[min_idx_int]);
            assert forall|k: int| i_int <= k < s.len() implies s[min_idx_int] <= s[k] by {};
            if k2 == min_idx_int {
                assert(s_after[k2] == s[i_int]);
                assert(s[min_idx_int] <= s[i_int]);
            } else {
                assert(s_after[k2] == s[k2]);
                assert(s[min_idx_int] <= s[k2]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],

        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed call to `lemma_swap_preserves_multiset` */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            sorted_prefix(a@, i as nat),
            partitioned(a@, i as nat),
        decreases a.len() - i
    {
        let ghost s_before = a@;
        let min_idx = find_min_index(a, i);

        a.swap(i, min_idx);

        proof {
            vstd::seq::lemma_swap_preserves_multiset(s_before, i as int, min_idx as int);
            selection_step_preserves_invs(s_before, i as nat, min_idx as nat);
        }

        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}