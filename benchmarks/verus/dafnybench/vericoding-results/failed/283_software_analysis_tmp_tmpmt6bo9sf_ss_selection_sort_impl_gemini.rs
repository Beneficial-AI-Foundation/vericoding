// <vc-preamble>
use vstd::prelude::*;

verus! {

fn find_min_index(a: &Vec<i32>, s: usize, e: usize) -> (min_i: usize)
    requires 
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures 
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
{
    assume(false);
    s
}

spec fn is_sorted(ss: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool
    decreases a.len(), b.len()
{
    a.len() == b.len() && 
    ((a.len() == 0 && b.len() == 0) ||  
     (exists|i: int, j: int| {
        0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j] && 
        is_permutation(
            a.subrange(0, i) + {if i < a.len() { a.subrange(i + 1, a.len() as int) } else { seq![] }},
            b.subrange(0, j) + {if j < b.len() { b.subrange(j + 1, b.len() as int) } else { seq![] }}
        )
     }))
}

spec fn is_permutation2(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.to_multiset() == b.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): updated vstd path */
proof fn lemma_sorted_prefix_preservation(s: Seq<i32>, i: int, min_idx: int)
    requires
        0 <= i < s.len(),
        i <= min_idx < s.len(),
        is_sorted(s.subrange(0, i)),
        forall|k: int| i <= k < s.len() ==> s[min_idx] <= s[k],
        forall|j: int, k: int| 0 <= j < i && i <= k < s.len() ==> s[j] <= s[k],
    ensures
        is_sorted(s.swap(i, min_idx).subrange(0, i + 1)),
{
    let s_new = s.swap(i, min_idx);
    vstd::seq_lib::lemma_swap_properties(s, i, min_idx);
    assert forall|j: int, k: int| 0 <= j <= k < i + 1 implies s_new[j] <= s_new[k] by {
        if k < i {
            assert(is_sorted(s.subrange(0, i)));
            assert(s_new[j] == s[j] && s_new[k] == s[k]);
        } else { // k == i
            assert(s_new[i] == s[min_idx]);
            if j < i {
                assert(s_new[j] == s[j]);
                assert(s[j] <= s[min_idx]);
            }
        }
    }
}

/* helper modified by LLM (iteration 3): updated vstd path */
proof fn lemma_partition_preservation(s: Seq<i32>, i: int, min_idx: int)
    requires
        0 <= i < s.len(),
        i <= min_idx < s.len(),
        forall|k: int| i <= k < s.len() ==> s[min_idx] <= s[k],
        forall|j: int, k: int| 0 <= j < i && i <= k < s.len() ==> s[j] <= s[k],
    ensures
        forall|j: int, k: int| 0 <= j < i + 1 && i + 1 <= k < s.len() ==> s.swap(i, min_idx)[j] <= s.swap(i, min_idx)[k],
{
    let s_new = s.swap(i, min_idx);
    vstd::seq_lib::lemma_swap_properties(s, i, min_idx);
    assert forall|j: int, k: int| 0 <= j < i + 1 && i + 1 <= k < s.len() implies s_new[j] <= s_new[k] by {
        if j < i {
            assert(s_new[j] == s[j]);
            if k == min_idx {
                assert(s_new[k] == s[i]);
                assert(s[j] <= s[i]);
            } else {
                assert(s_new[k] == s[k]);
                assert(s[j] <= s[k]);
            }
        } else { // j == i
            assert(s_new[j] == s[min_idx]);
            if k == min_idx {
                assert(s_new[k] == s[i]);
                assert(s[min_idx] <= s[i]);
            } else {
                assert(s_new[k] == s[k]);
                assert(s[min_idx] <= s[k]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(ns: &mut Vec<i32>) 
    requires old(ns).len() >= 0
    ensures 
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed compilation error by qualifying lemma path */
    let mut i: usize = 0;
    let len = ns.len();
    while i < len
        invariant
            len == old(ns).len(),
            ns.len() == len,
            0 <= i <= len,
            is_permutation2(ns@, old(ns)@),
            is_sorted(ns@.subrange(0, i as int)),
            forall|j: int, k: int| 0 <= j < i && i <= k < ns.len() ==> ns@[j] <= ns@[k],
        decreases len - i,
    {
        if i < len - 1 {
            let min_idx = find_min_index(ns, i, len);
            ghost {
                vstd::multiset::lemma_swap_to_multiset(ns@, i as int, min_idx as int);
                lemma_sorted_prefix_preservation(ns@, i as int, min_idx as int);
                lemma_partition_preservation(ns@, i as int, min_idx as int);
            }
            ns.swap(i, min_idx);
        } else {
            ghost {
                let s = ns@;
                assert(is_sorted(s.subrange(0, i as int)));
                assert(is_sorted(s.subrange(0, i as int + 1))) by {
                    assert(s.subrange(0, i as int) == s.subrange(0, i as int + 1));
                }
                assert(is_sorted(ns@));

                assert forall|j: int, k: int| 0 <= j < i + 1 && i + 1 <= k < ns.len()
                implies ns@[j] <= ns@[k] by {
                }
            }
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}