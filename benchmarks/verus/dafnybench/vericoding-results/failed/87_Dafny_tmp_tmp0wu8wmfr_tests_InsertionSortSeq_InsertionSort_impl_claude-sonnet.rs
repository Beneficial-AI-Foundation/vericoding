use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
spec fn is_sorted_up_to(s: Seq<int>, k: int) -> bool {
    forall|p: int, q: int| 0 <= p < q < k ==> s[p] <= s[q]
}

spec fn insert_at_correct_position(s: Seq<int>, val: int, pos: int) -> bool {
    (pos == 0 || s[pos - 1] <= val) &&
    (pos == s.len() || val <= s[pos])
}

proof fn lemma_sorted_slice_remains_sorted(s: Seq<int>, start: int, end: int)
    requires
        is_sorted(s),
        0 <= start <= end <= s.len(),
    ensures
        is_sorted(s.subrange(start, end)),
{
}

proof fn lemma_insert_preserves_sorted(s: Seq<int>, val: int, pos: int)
    requires
        is_sorted(s),
        0 <= pos <= s.len(),
        insert_at_correct_position(s, val, pos),
    ensures
        is_sorted(s.insert(pos, val)),
{
}

proof fn lemma_multiset_insert_remove(s: Seq<int>, i: int)
    requires 0 <= i < s.len()
    ensures s.to_multiset() == s.remove(i).insert(i, s[i]).to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// <vc-code>
{
    let mut result = s;
    let mut i: usize = 1;
    
    while i < result.len()
        invariant
            result.to_multiset() == s.to_multiset(),
            is_sorted_up_to(result, i as int),
            0 <= i <= result.len(),
    {
        let key = result@[i];
        let mut j = i;
        
        while j > 0 && result@[j - 1] > key
            invariant
                result.to_multiset() == s.to_multiset(),
                is_sorted_up_to(result, i as int),
                0 <= j <= i,
                result@[i] == key,
                forall|k: int| j < k < i ==> result[k] > key,
                forall|k: int| 0 <= k < j ==> result[k] <= key || k == i,
        {
            result = result.update(j as int, result@[j - 1]);
            j = j - 1;
        }
        
        result = result.update(j as int, key);
        
        assert(is_sorted_up_to(result, (i + 1) as int)) by {
            assert(forall|p: int, q: int| 0 <= p < q < (i + 1) as int ==> result[p] <= result[q]);
        }
        
        i = i + 1;
    }
    
    assert(is_sorted(result)) by {
        assert(is_sorted_up_to(result, result.len() as int));
        assert(forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] <= result[q]);
    }
    
    result
}
// </vc-code>

fn main() {}

}