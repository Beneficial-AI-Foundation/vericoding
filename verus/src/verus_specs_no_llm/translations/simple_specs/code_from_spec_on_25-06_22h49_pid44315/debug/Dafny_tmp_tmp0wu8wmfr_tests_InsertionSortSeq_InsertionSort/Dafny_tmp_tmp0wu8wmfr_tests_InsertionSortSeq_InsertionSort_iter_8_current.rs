use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s.spec_index(p) <= s.spec_index(q)
}

spec fn multiset(s: Seq<int>) -> Multiset<int> {
    s.to_multiset()
}

fn InsertionSort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        multiset(r) == multiset(s),
        IsSorted(r)
{
    let mut result = Seq::empty();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            multiset(result) == multiset(s.subrange(0, i as int)),
            IsSorted(result)
        decreases s.len() - i
    {
        let elem = s[i];
        let old_result = result;
        result = insert_sorted(result, elem);
        
        proof {
            // Prove multiset invariant is maintained
            assert(multiset(old_result) == multiset(s.subrange(0, i as int)));
            assert(multiset(result) == multiset(old_result).insert(elem));
            assert(elem == s.spec_index(i as int));
            
            // Show that adding elem gives us the next subrange
            let next_subrange = s.subrange(0, (i + 1) as int);
            let curr_subrange = s.subrange(0, i as int);
            
            // Key insight: prove subrange relationship
            assert(curr_subrange.len() == i);
            assert(next_subrange.len() == i + 1);
            assert forall|k: int| 0 <= k < i implies curr_subrange.spec_index(k) == next_subrange.spec_index(k) by {
                assert(curr_subrange.spec_index(k) == s.spec_index(k));
                assert(next_subrange.spec_index(k) == s.spec_index(k));
            };
            assert(next_subrange.spec_index(i as int) == s.spec_index(i as int));
            assert(next_subrange.spec_index(i as int) == elem);
            
            // This proves the multiset relationship
            assert(multiset(next_subrange) == multiset(curr_subrange).insert(elem));
            assert(multiset(result) == multiset(next_subrange));
        }
        
        i = i + 1;
    }
    
    proof {
        // Final proof that we've processed the entire sequence
        assert(i == s.len());
        assert(s.subrange(0, s.len() as int) =~= s);
        assert(multiset(result) == multiset(s));
    }
    
    result
}

fn insert_sorted(s: Seq<int>, elem: int) -> (r: Seq<int>)
    requires IsSorted(s)
    ensures 
        IsSorted(r),
        multiset(r) == multiset(s).insert(elem)
{
    let mut pos = 0;
    
    while pos < s.len() && s[pos] <= elem
        invariant
            0 <= pos <= s.len(),
            forall|k: int| 0 <= k < pos ==> s.spec_index(k) <= elem
        decreases s.len() - pos
    {
        pos = pos + 1;
    }
    
    let left = s.subrange(0, pos as int);
    let right = s.subrange(pos as int, s.len() as int);
    let middle = seq![elem];
    let result = left.add(middle).add(right);
    
    proof {
        // First establish the basic structure
        assert(s =~= left.add(right));
        assert(left.len() == pos);
        assert(middle.len() == 1);
        assert(middle.spec_index(0) == elem);
        assert(result.len() == s.len() + 1);
        
        // Prove multiset equality step by step
        assert(multiset(s) == multiset(left).add(multiset(right)));
        assert(multiset(middle) == multiset![elem]);
        assert(multiset(result) == multiset(left).add(multiset(middle)).add(multiset(right)));
        assert(multiset(result) == multiset(s).insert(elem));
        
        // Prove that the result is sorted
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            let left_len = left.len();
            let middle_start = left_len;
            let right_start = left_len + 1;
            
            // Establish indexing relationships
            assert forall|i: int| 0 <= i < left_len implies result.spec_index(i) == left.spec_index(i) by {};
            assert(result.spec_index(middle_start) == elem);
            assert forall|i: int| right_start <= i < result.len() implies result.spec_index(i) == right.spec_index(i - right_start) by {};
            
            if q < left_len {
                // Both in left part - use original sortedness
                assert(result.spec_index(p) == s.spec_index(p));
                assert(result.spec_index(q) == s.spec_index(q));
            } else if p >= right_start {
                // Both in right part - use original sortedness
                let right_p = p - right_start;
                let right_q = q - right_start;
                assert(0 <= right_p < right_q < right.len());
                assert(result.spec_index(p) == s.spec_index(pos + right_p));
                assert(result.spec_index(q) == s.spec_index(pos + right_q));
            } else if p < left_len && q == middle_start {
                // p in left, q is middle element
                assert(result.spec_index(p) == s.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(p < pos);
                // From loop invariant
                assert(s.spec_index(p) <= elem);
            } else if p == middle_start && q >= right_start {
                // p is middle, q in right
                assert(result.spec_index(p) == elem);
                let right_q = q - right_start;
                assert(result.spec_index(q) == s.spec_index(pos + right_q));
                if pos < s.len() {
                    // Loop terminated because s[pos] > elem
                    assert(!(s.spec_index(pos) <= elem));
                    assert(elem < s.spec_index(pos));
                    // Use original sortedness
                    assert(s.spec_index(pos) <= s.spec_index(pos + right_q));
                    assert(elem < s.spec_index(pos + right_q));
                }
            } else if p < left_len && q >= right_start {
                // p in left, q in right - transitivity through middle
                assert(result.spec_index(p) == s.spec_index(p));
                let right_q = q - right_start;
                assert(result.spec_index(q) == s.spec_index(pos + right_q));
                
                // Chain: s[p] <= elem < s[pos] <= s[pos + right_q]
                assert(p < pos);
                assert(s.spec_index(p) <= elem);
                if pos < s.len() {
                    assert(elem < s.spec_index(pos));
                    assert(s.spec_index(pos) <= s.spec_index(pos + right_q));
                    assert(s.spec_index(p) <= s.spec_index(pos + right_q));
                }
            }
        };
    }
    
    result
}

}