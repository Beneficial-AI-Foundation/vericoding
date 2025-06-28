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
            let curr_subrange = s.subrange(0, i as int);
            let next_subrange = s.subrange(0, (i + 1) as int);
            
            // Key insight: next_subrange extends curr_subrange with one element
            assert(next_subrange.len() == curr_subrange.len() + 1);
            assert(next_subrange.spec_index((next_subrange.len() - 1) as int) == elem);
            
            // Prove that curr_subrange + elem = next_subrange in terms of multisets
            assert forall|j: int| 0 <= j < curr_subrange.len() implies 
                curr_subrange.spec_index(j) == next_subrange.spec_index(j) by {}
            
            // Use the ensures clause of insert_sorted
            assert(multiset(result) == multiset(old_result).insert(elem));
            assert(multiset(old_result) == multiset(curr_subrange));
            
            // Prove multiset equality step by step
            let curr_ms = multiset(curr_subrange);
            let next_ms = multiset(next_subrange);
            assert(next_ms == curr_ms.insert(elem));
            assert(multiset(result) == next_ms);
        }
        
        i = i + 1;
    }
    
    proof {
        // Final proof that we've processed the entire sequence
        assert(i == s.len());
        assert(s.subrange(0, s.len() as int) =~= s);
        assert(multiset(result) == multiset(s.subrange(0, s.len() as int)));
        assert(multiset(s.subrange(0, s.len() as int)) == multiset(s));
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
    let result = left + middle + right;
    
    proof {
        // Prove that s equals left + right
        assert(s =~= left + right);
        
        // Prove multiset equality step by step
        assert(multiset(left + right) == multiset(left).add(multiset(right)));
        assert(multiset(s) == multiset(left).add(multiset(right)));
        assert(multiset(middle) == multiset(seq![elem]));
        assert(multiset(middle).count(elem) == 1);
        assert(multiset(result) == multiset(left).add(multiset(middle)).add(multiset(right)));
        assert(multiset(result) == multiset(s).insert(elem));
        
        // Key properties from the loop condition
        assert(forall|k: int| 0 <= k < pos ==> s.spec_index(k) <= elem);
        assert(pos == s.len() || s.spec_index(pos) > elem);
        
        // Prove sortedness by comprehensive case analysis
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            let left_len = left.len();
            let middle_pos = left_len;
            let right_start = left_len + 1;
            
            assert(left_len == pos);
            assert(middle_pos == pos);
            assert(right_start == pos + 1);
            
            if q < left_len {
                // Both indices in left part - use original sortedness
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == left.spec_index(q));
                assert(left.spec_index(p) == s.spec_index(p));
                assert(left.spec_index(q) == s.spec_index(q));
                assert(s.spec_index(p) <= s.spec_index(q)); // from IsSorted(s)
            } else if p >= right_start {
                // Both indices in right part - use original sortedness
                let right_p = p - right_start;
                let right_q = q - right_start;
                assert(0 <= right_p < right_q < right.len());
                assert(result.spec_index(p) == right.spec_index(right_p));
                assert(result.spec_index(q) == right.spec_index(right_q));
                assert(right.spec_index(right_p) == s.spec_index(pos + right_p));
                assert(right.spec_index(right_q) == s.spec_index(pos + right_q));
                assert(s.spec_index(pos + right_p) <= s.spec_index(pos + right_q)); // from IsSorted(s)
            } else if p < left_len && q == middle_pos {
                // p in left, q is the inserted element
                assert(result.spec_index(p) == s.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(p < pos);
                assert(s.spec_index(p) <= elem); // from loop invariant
            } else if p == middle_pos && q >= right_start {
                // p is the inserted element, q in right
                assert(result.spec_index(p) == elem);
                let right_q = q - right_start;
                assert(result.spec_index(q) == right.spec_index(right_q));
                assert(right.spec_index(right_q) == s.spec_index(pos + right_q));
                if pos < s.len() {
                    assert(elem < s.spec_index(pos)); // from loop termination condition
                    assert(s.spec_index(pos) <= s.spec_index(pos + right_q)); // from IsSorted(s)
                    assert(elem <= s.spec_index(pos + right_q));
                }
            } else if p < left_len && q >= right_start {
                // p in left, q in right
                assert(result.spec_index(p) == s.spec_index(p));
                let right_q = q - right_start;
                assert(result.spec_index(q) == s.spec_index(pos + right_q));
                assert(p < pos);
                assert(s.spec_index(p) <= elem); // from loop invariant
                if pos < s.len() {
                    assert(elem < s.spec_index(pos)); // from loop termination
                    assert(s.spec_index(pos) <= s.spec_index(pos + right_q)); // from IsSorted(s)
                    assert(s.spec_index(p) <= s.spec_index(pos + right_q));
                }
            }
        };
    }
    
    result
}

}