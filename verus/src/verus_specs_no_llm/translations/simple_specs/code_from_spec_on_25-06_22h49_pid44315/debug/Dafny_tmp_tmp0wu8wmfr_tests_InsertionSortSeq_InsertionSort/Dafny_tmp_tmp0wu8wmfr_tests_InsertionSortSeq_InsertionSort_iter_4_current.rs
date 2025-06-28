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
            assert(s.subrange(0, (i + 1) as int) == s.subrange(0, i as int).push(elem));
            assert(multiset(s.subrange(0, (i + 1) as int)) == multiset(s.subrange(0, i as int)).insert(elem));
            assert(multiset(old_result) == multiset(s.subrange(0, i as int)));
            assert(multiset(result) == multiset(old_result).insert(elem));
            assert(multiset(result) == multiset(s.subrange(0, i as int)).insert(elem));
            assert(multiset(result) == multiset(s.subrange(0, (i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s.subrange(0, i as int) == s);
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
        // First establish basic facts about the structure
        assert(s == left.add(right));
        assert(result.len() == left.len() + 1 + right.len());
        assert(result.len() == s.len() + 1);
        
        // Prove multiset equality
        assert(multiset(s) == multiset(left).add(multiset(right)));
        assert(multiset(middle) == Multiset::singleton(elem));
        assert(multiset(result) == multiset(left).add(multiset(middle)).add(multiset(right)));
        assert(multiset(result) == multiset(s).insert(elem));
        
        // Prove that the result is sorted
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            let left_len = left.len();
            
            if q < left_len {
                // Both indices are in the left part
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == left.spec_index(q));
                assert(left.spec_index(p) <= left.spec_index(q));
            } else if p >= left_len + 1 {
                // Both indices are in the right part
                let right_p = p - left_len - 1;
                let right_q = q - left_len - 1;
                assert(0 <= right_p < right_q < right.len());
                assert(result.spec_index(p) == right.spec_index(right_p));
                assert(result.spec_index(q) == right.spec_index(right_q));
                assert(right.spec_index(right_p) <= right.spec_index(right_q));
            } else if p < left_len && q == left_len {
                // p is in left part, q is the inserted element
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(p < pos);
                assert(left.spec_index(p) == s.spec_index(p));
                assert(s.spec_index(p) <= elem);
            } else if p == left_len && q > left_len {
                // p is the inserted element, q is in right part
                assert(result.spec_index(p) == elem);
                let right_q = q - left_len - 1;
                assert(0 <= right_q < right.len());
                assert(result.spec_index(q) == right.spec_index(right_q));
                
                if pos < s.len() {
                    assert(!(s[pos] <= elem));
                    assert(elem < s[pos]);
                    assert(s[pos] == right.spec_index(0));
                    assert(right.spec_index(0) <= right.spec_index(right_q));
                    assert(elem < right.spec_index(right_q));
                }
            } else if p < left_len && q > left_len {
                // p is in left part, q is in right part  
                assert(result.spec_index(p) == left.spec_index(p));
                let right_q = q - left_len - 1;
                assert(0 <= right_q < right.len());
                assert(result.spec_index(q) == right.spec_index(right_q));
                
                assert(p < pos);
                assert(left.spec_index(p) == s.spec_index(p));
                assert(s.spec_index(p) <= elem);
                
                if pos < s.len() {
                    assert(!(s[pos] <= elem));
                    assert(elem < s[pos]);
                    assert(s[pos] == right.spec_index(0));
                    assert(right.spec_index(0) <= right.spec_index(right_q));
                    assert(s.spec_index(p) <= elem);
                    assert(elem < right.spec_index(right_q));
                    assert(s.spec_index(p) < right.spec_index(right_q));
                }
            }
        }
    }
    
    result
}

}