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
        i = i + 1;
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
        // Prove multiset equality using built-in lemmas
        assert(multiset(result) == multiset(s).insert(elem));
        
        // Prove that the result is sorted
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            let left_len = left.len();
            let middle_pos = left_len;
            
            if q < left_len {
                // Both in left part
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == left.spec_index(q));
            } else if p >= left_len + 1 {
                // Both in right part
                let right_p = p - left_len - 1;
                let right_q = q - left_len - 1;
                assert(result.spec_index(p) == right.spec_index(right_p));
                assert(result.spec_index(q) == right.spec_index(right_q));
            } else if p < left_len && q == middle_pos {
                // p in left, q is elem
                assert(result.spec_index(p) == s.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(p < pos);
            } else if p == middle_pos && q > middle_pos {
                // p is elem, q in right
                assert(result.spec_index(p) == elem);
                if pos < s.len() {
                    assert(elem < s.spec_index(pos));
                    assert(s.spec_index(pos) == right.spec_index(0));
                    assert(result.spec_index(q) == right.spec_index(q - left_len - 1));
                    assert(right.spec_index(0) <= right.spec_index(q - left_len - 1));
                }
            } else if p < left_len && q > middle_pos {
                // p in left, q in right
                assert(result.spec_index(p) == s.spec_index(p));
                assert(result.spec_index(q) == right.spec_index(q - left_len - 1));
                assert(p < pos);
                if pos < s.len() {
                    assert(s.spec_index(p) <= elem);
                    assert(elem < s.spec_index(pos));
                    assert(s.spec_index(pos) <= result.spec_index(q));
                }
            }
        }
    }
    
    result
}

}