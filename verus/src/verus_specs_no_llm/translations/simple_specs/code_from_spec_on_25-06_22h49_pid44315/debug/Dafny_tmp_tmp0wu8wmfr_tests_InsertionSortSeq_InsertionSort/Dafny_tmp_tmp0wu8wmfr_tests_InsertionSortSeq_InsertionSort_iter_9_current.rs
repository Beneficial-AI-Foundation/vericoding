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
            let curr_subrange = s.subrange(0, i as int);
            let next_subrange = s.subrange(0, (i + 1) as int);
            
            // Key lemma: next_subrange is curr_subrange + elem
            assert(next_subrange.len() == curr_subrange.len() + 1);
            assert(multiset(next_subrange) == multiset(curr_subrange).insert(elem));
        }
        
        i = i + 1;
    }
    
    proof {
        // Final proof that we've processed the entire sequence
        assert(i == s.len());
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
    let result = left + middle + right;
    
    proof {
        // Prove multiset equality
        assert(s =~= left + right);
        assert(multiset(result) == multiset(left).add(multiset(middle)).add(multiset(right)));
        assert(multiset(result) == multiset(s).insert(elem));
        
        // Prove sortedness by cases
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            let left_len = left.len();
            let middle_pos = left_len;
            let right_start = left_len + 1;
            
            if q < left_len {
                // Both in left part
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == left.spec_index(q));
                assert(left.spec_index(p) == s.spec_index(p));
                assert(left.spec_index(q) == s.spec_index(q));
            } else if p >= right_start {
                // Both in right part
                let right_p = p - right_start;
                let right_q = q - right_start;
                assert(result.spec_index(p) == right.spec_index(right_p));
                assert(result.spec_index(q) == right.spec_index(right_q));
            } else if p < left_len && q == middle_pos {
                // p in left, q is middle
                assert(result.spec_index(p) == s.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(p < pos);
            } else if p == middle_pos && q >= right_start {
                // p is middle, q in right
                assert(result.spec_index(p) == elem);
                if pos < s.len() {
                    assert(elem < s.spec_index(pos));
                }
            } else if p < left_len && q >= right_start {
                // p in left, q in right
                assert(result.spec_index(p) == s.spec_index(p));
                assert(p < pos);
                if pos < s.len() {
                    assert(s.spec_index(p) <= elem);
                    assert(elem < s.spec_index(pos));
                }
            }
        };
    }
    
    result
}

}