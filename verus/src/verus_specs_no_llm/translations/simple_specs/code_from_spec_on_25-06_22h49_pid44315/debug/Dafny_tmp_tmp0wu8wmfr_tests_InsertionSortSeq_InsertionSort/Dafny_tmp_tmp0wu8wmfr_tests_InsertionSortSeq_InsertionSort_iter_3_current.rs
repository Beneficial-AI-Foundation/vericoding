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
            let old_i = i;
            assert(s.subrange(0, (old_i + 1) as int) == s.subrange(0, old_i as int).push(elem));
            assert(multiset(s.subrange(0, (old_i + 1) as int)) == multiset(s.subrange(0, old_i as int)).insert(elem));
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
        // Prove that the result is sorted
        assert forall|p: int, q: int| 0 <= p < q < result.len() implies result.spec_index(p) <= result.spec_index(q) by {
            let left_len = left.len();
            let middle_len = 1int;
            
            if q < left_len {
                // Both indices are in the left part
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == left.spec_index(q));
                assert(left.spec_index(p) <= left.spec_index(q)) by {
                    assert(IsSorted(s));
                    assert(left == s.subrange(0, pos as int));
                }
            } else if p >= left_len + middle_len {
                // Both indices are in the right part
                let right_p = p - left_len - middle_len;
                let right_q = q - left_len - middle_len;
                assert(result.spec_index(p) == right.spec_index(right_p));
                assert(result.spec_index(q) == right.spec_index(right_q));
                assert(right.spec_index(right_p) <= right.spec_index(right_q)) by {
                    assert(IsSorted(s));
                    assert(right == s.subrange(pos as int, s.len() as int));
                }
            } else if p < left_len && q == left_len {
                // p is in left part, q is the inserted element
                assert(result.spec_index(p) == left.spec_index(p));
                assert(result.spec_index(q) == elem);
                assert(left.spec_index(p) <= elem) by {
                    assert(p < pos);
                }
            } else if p == left_len && q > left_len {
                // p is the inserted element, q is in right part
                assert(result.spec_index(p) == elem);
                if q < left_len + middle_len {
                    // This case is impossible since middle_len = 1
                    assert(false);
                } else {
                    let right_q = q - left_len - middle_len;
                    assert(result.spec_index(q) == right.spec_index(right_q));
                    if pos < s.len() {
                        assert(!(s[pos] <= elem));
                        assert(elem < s[pos]);
                        assert(s[pos] == right.spec_index(0));
                        assert(right.spec_index(0) <= right.spec_index(right_q)) by {
                            assert(IsSorted(right));
                        }
                    }
                }
            } else if p < left_len && q > left_len + middle_len - 1 {
                // p is in left part, q is in right part
                assert(result.spec_index(p) == left.spec_index(p));
                let right_q = q - left_len - middle_len;
                assert(result.spec_index(q) == right.spec_index(right_q));
                assert(left.spec_index(p) <= elem);
                if pos < s.len() {
                    assert(elem < s[pos]);
                    assert(s[pos] == right.spec_index(0));
                    assert(right.spec_index(0) <= right.spec_index(right_q)) by {
                        assert(IsSorted(right));
                    }
                }
            }
        }
        
        // Prove multiset equality
        assert(multiset(result) == multiset(left).add(multiset(middle)).add(multiset(right)));
        assert(multiset(s) == multiset(left).add(multiset(right))) by {
            assert(s == left.add(right));
        }
        assert(multiset(middle) == multiset(seq![elem]));
        assert(multiset(seq![elem]).len() == 1);
        assert(multiset(result) == multiset(s).insert(elem));
    }
    
    result
}

}