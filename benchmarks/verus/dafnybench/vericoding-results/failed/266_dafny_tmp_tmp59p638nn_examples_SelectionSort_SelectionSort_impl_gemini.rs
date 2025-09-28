// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}
// </vc-preamble>

// <vc-helpers>
fn find_min_index(a: &Vec<int>, start: int) -> (min_idx: usize)
    requires
        0 <= start < a.len(),
    ensures
        start <= (min_idx as int) < a.len(),
        forall|k: int| start <= k < a.len() ==> a@[min_idx as int] <= a@[k],
{
    let mut min_idx = start as usize;
    let mut i = start + 1;
    while i < a.len() as int
        invariant
            start + 1 <= i <= a.len(),
            start <= (min_idx as int) < i,
            forall|k: int| start <= k < i ==> a@[min_idx as int] <= a@[k],
        decreases (a.len() as int) - i
    {
        if a[i as usize] < a[min_idx] {
            min_idx = i as usize;
        }
        i = i + 1;
    }
    min_idx
}

/* helper modified by LLM (iteration 4): expanded proof in lemma */
proof fn lemma_selection_swap(s: Seq<int>, i: int, m: int)
    requires
        0 <= i < s.len(),
        i <= m < s.len(),
        ordered(s, 0, i),
        (forall|j: int, k: int| 0 <= j < i && i <= k < s.len() ==> s[j] <= s[k]),
        (forall|k: int| i <= k < s.len() ==> s[m] <= s[k]),
    ensures
        ordered(s.swap(i, m), 0, i + 1),
        (forall|j: int, k: int| 0 <= j < i + 1 && i + 1 <= k < s.len() ==> s.swap(i, m)[j] <= s.swap(i, m)[k]),
{
    let s_new = s.swap(i, m);
    
    assert forall |p: int| 0 < p < i + 1 implies s_new[p-1] <= s_new[p] by {
        if p < i {
            assert(s[p-1] <= s[p]);
        } else { // p == i
            if i > 0 {
                assert(s[i-1] <= s[m]);
            }
        }
    }

    assert forall |j: int, k: int| 0 <= j < i + 1 && i + 1 <= k < s.len() implies s_new[j] <= s_new[k] by {
        if j < i {
            if k == m {
                assert(s[j] <= s[i]);
            } else {
                assert(s[j] <= s[k]);
            }
        } else { // j == i
            if k == m {
                assert(s[m] <= s[i]);
            } else {
                assert(s[m] <= s[k]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed parsing error by changing a@ to a.view() */
{
    let len = a.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            a.len() == len,
            ordered(a@, 0, i as int),
            (forall|j: int, k: int| 0 <= j < (i as int) && (i as int) <= k < (len as int) ==> a@[j] <= a@[k]),
            a@.to_multiset() === old(a)@.to_multiset(),
        decreases len - i
    {
        let min_idx = find_min_index(a, i as int);

        ghost {
            let s = a.view();
            lemma_selection_swap(s, i as int, min_idx as int);
        }

        a.swap(i, min_idx);

        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}