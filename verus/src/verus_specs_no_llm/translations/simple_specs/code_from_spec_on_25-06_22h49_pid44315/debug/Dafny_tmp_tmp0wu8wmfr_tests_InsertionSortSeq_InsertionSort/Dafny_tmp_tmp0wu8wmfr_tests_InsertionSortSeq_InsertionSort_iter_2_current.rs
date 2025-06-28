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
    let mut i = 0int;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            multiset(result) == multiset(s.subrange(0, i)),
            IsSorted(result)
    {
        let elem = s[i];
        result = insert_sorted(result, elem);
        i = i + 1;
        
        proof {
            assert(s.subrange(0, i) == s.subrange(0, i - 1).push(elem));
            assert(multiset(s.subrange(0, i)) == multiset(s.subrange(0, i - 1)).insert(elem));
        }
    }
    
    proof {
        assert(s.subrange(0, i) == s);
    }
    
    result
}

fn insert_sorted(s: Seq<int>, elem: int) -> (r: Seq<int>)
    requires IsSorted(s)
    ensures 
        IsSorted(r),
        multiset(r) == multiset(s).insert(elem)
{
    let mut pos = 0int;
    
    while pos < s.len() && s[pos] <= elem
        invariant
            0 <= pos <= s.len(),
            forall|k: int| 0 <= k < pos ==> s.spec_index(k) <= elem
    {
        pos = pos + 1;
    }
    
    let left = s.subrange(0, pos);
    let right = s.subrange(pos, s.len() as int);
    let result = left.push(elem).add(right);
    
    proof {
        // Prove that the result is sorted
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            if q < left.len() {
                // Both indices are in the left part
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == left.spec_index(q));
            } else if p >= left.len() + 1 {
                // Both indices are in the right part
                let right_p = p - left.len() - 1;
                let right_q = q - left.len() - 1;
                assert(result.spec_index(p) == right.spec_index(right_p));
                assert(result.spec_index(q) == right.spec_index(right_q));
            } else if p < left.len() && q == left.len() {
                // p is in left part, q is the inserted element
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(p < pos);
            } else if p == left.len() && q > left.len() {
                // p is the inserted element, q is in right part
                assert(result.spec_index(p) == elem);
                let right_q = q - left.len() - 1;
                assert(result.spec_index(q) == right.spec_index(right_q));
                if pos < s.len() {
                    assert(elem <= s.spec_index(pos));
                    assert(s.spec_index(pos) == right.spec_index(0));
                }
            } else if p < left.len() && q > left.len() {
                // p is in left part, q is in right part
                assert(result.spec_index(p) == left.spec_index(p));
                let right_q = q - left.len() - 1;
                assert(result.spec_index(q) == right.spec_index(right_q));
            }
        }
        
        // Prove multiset equality
        assert(multiset(result) == multiset(left).add(multiset(seq![elem])).add(multiset(right)));
        assert(multiset(s) == multiset(left).add(multiset(right)));
        assert(multiset(result) == multiset(s).insert(elem));
    }
    
    result
}

}