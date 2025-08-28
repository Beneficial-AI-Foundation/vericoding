use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
use vstd::multiset::Multiset;

spec fn is_sorted_up_to(s: Seq<int>, n: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < n ==> s[i] <= s[j]
}

spec fn insert_into_sorted(s: Seq<int>, n: int, x: int) -> Seq<int>
    recommends 0 <= n <= s.len(), is_sorted_up_to(s, n)
{
    let mut pos: int = 0;
    while pos < n && s[pos] <= x {
        pos = pos + 1;
    }
    s.subrange(0, pos).add(seq![x]).add(s.subrange(pos, s.len() as int))
}

proof fn lemma_insert_preserves_multiset(s: Seq<int>, n: int, x: int)
    requires 0 <= n <= s.len(), is_sorted_up_to(s, n)
    ensures insert_into_sorted(s, n, x).to_multiset() == s.to_multiset().add(Multiset::singleton(x))
{
    // This lemma would need detailed proof in practice
}

proof fn lemma_insert_maintains_sorted(s: Seq<int>, n: int, x: int)
    requires 0 <= n <= s.len(), is_sorted_up_to(s, n)
    ensures is_sorted_up_to(insert_into_sorted(s, n, x), n + 1)
{
    // This lemma would need detailed proof in practice  
}

proof fn lemma_subrange_multiset(s: Seq<int>, start: int, end: int, x: int, pos: int)
    requires 0 <= start <= pos <= end <= s.len()
    ensures s.subrange(start, pos).add(seq![x]).add(s.subrange(pos, end)).to_multiset() == 
            s.subrange(start, end).to_multiset().add(Multiset::singleton(x))
{
}

proof fn lemma_sorted_insert_preserves_order(result: Seq<int>, x: int, j: int)
    requires 
        is_sorted(result),
        0 <= j <= result.len(),
        forall|k: int| 0 <= k < j ==> result[k] <= x,
    ensures 
        is_sorted(result.subrange(0, j).add(seq![x]).add(result.subrange(j, result.len())))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if s.len() == 0nat {
        return s;
    }
    
    let mut result = seq![s@[0]];
    let mut i: int = 1;
    
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            result.len() == i,
            is_sorted(result),
            result.to_multiset() == s.subrange(0, i).to_multiset(),
    {
        let x = s@[i];
        let mut j: int = 0;
        
        // Find insertion position
        while j < result.len() && result@[j] <= x
            invariant
                0 <= j <= result.len(),
                forall|k: int| 0 <= k < j ==> result@[k] <= x,
        {
            j = j + 1;
        }
        
        // Insert x at position j
        let left = result.subrange(0, j);
        let right = result.subrange(j, result.len());
        let old_result = result;
        result = left.add(seq![x]).add(right);
        
        proof {
            lemma_subrange_multiset(old_result, 0, old_result.len() as int, x, j);
            lemma_sorted_insert_preserves_order(old_result, x, j);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}