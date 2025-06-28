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
        result = insert_sorted(result, elem);
        
        proof {
            // Prove multiset invariant is maintained
            assert(multiset(result) == multiset(s.subrange(0, (i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    proof {
        // Final proof that we've processed the entire sequence
        assert(s.subrange(0, s.len() as int) =~= s);
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
        // Prove multiset equality step by step
        assert(s =~= left.add(right));
        assert(multiset(s) == multiset(left.add(right)));
        assert(multiset(left.add(right)) == multiset(left).add(multiset(right)));
        assert(multiset(middle) == multiset![elem]);
        assert(multiset(result) == multiset(left.add(middle).add(right)));
        assert(multiset(result) == multiset(left).add(multiset(middle)).add(multiset(right)));
        assert(multiset(result) == multiset(left).add(multiset![elem]).add(multiset(right)));
        assert(multiset(result) == multiset(s).insert(elem));
        
        // Prove that the result is sorted
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            let left_len = left.len();
            let middle_start = left_len;
            let right_start = left_len + 1;
            
            if q < left_len {
                // Both indices are in the left part
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == left.spec_index(q));
                assert(left.spec_index(p) == s.spec_index(p));
                assert(left.spec_index(q) == s.spec_index(q));
                assert(IsSorted(s));
            } else if p >= right_start {
                // Both indices are in the right part
                let right_p = p - right_start;
                let right_q = q - right_start;
                assert(0 <= right_p < right_q < right.len());
                assert(result.spec_index(p) == right.spec_index(right_p));
                assert(result.spec_index(q) == right.spec_index(right_q));
                assert(right.spec_index(right_p) == s.spec_index(pos + right_p));
                assert(right.spec_index(right_q) == s.spec_index(pos + right_q));
                assert(IsSorted(s));
            } else if p < left_len && q == middle_start {
                // p in left part, q is the inserted element
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(left.spec_index(p) == s.spec_index(p));
                assert(p < pos);
                // From loop invariant, s[p] <= elem
            } else if p == middle_start && q >= right_start {
                // p is the inserted element, q in right part
                assert(result.spec_index(p) == elem);
                let right_q = q - right_start;
                assert(result.spec_index(q) == right.spec_index(right_q));
                assert(right.spec_index(right_q) == s.spec_index(pos + right_q));
                // From loop condition, either pos >= s.len() or elem < s[pos]
                if pos < s.len() {
                    assert(elem < s.spec_index(pos));
                    assert(s.spec_index(pos) <= s.spec_index(pos + right_q));
                }
            } else if p < left_len && q >= right_start {
                // p in left part, q in right part
                assert(result.spec_index(p) == s.spec_index(p));
                let right_q = q - right_start;
                assert(result.spec_index(q) == s.spec_index(pos + right_q));
                assert(p < pos);
                assert(pos + right_q < s.len());
                assert(IsSorted(s));
                assert(s.spec_index(p) <= s.spec_index(pos + right_q));
            }
        };
        assert(IsSorted(result));
    }
    
    result
}

}