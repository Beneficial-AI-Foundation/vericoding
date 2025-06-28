use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int| 0 <= u < s.len() ==> s[u] >= 0
}

fn firstNegative(v: Vec<int>) -> (b: bool, i: int)
    ensures
        b <==> exists |k: int| 0 <= k < v.len() && v@[k] < 0,
        b ==> 0 <= i < v.len() && v@[i] < 0 && positive(v@.subrange(0, i))
{
    let mut index: usize = 0;
    
    while index < v.len()
        invariant
            0 <= index <= v.len(),
            forall |j: int| 0 <= j < index ==> v@[j] >= 0,
    {
        if v[index] < 0 {
            // Help Verus understand the subrange relationship
            assert(v@.subrange(0, index as int).len() == index);
            assert(forall |u: int| 0 <= u < (index as int) ==> 
                v@.subrange(0, index as int)[u] == v@[u]);
            
            // Now prove positive holds for the subrange
            assert(positive(v@.subrange(0, index as int))) by {
                let subseq = v@.subrange(0, index as int);
                assert(forall |u: int| 0 <= u < subseq.len() ==> subseq[u] >= 0) by {
                    assert(forall |u: int| 0 <= u < (index as int) ==> {
                        &&& subseq[u] == v@[u]
                        &&& v@[u] >= 0  // from loop invariant
                        &&& subseq[u] >= 0
                    });
                };
            };
            
            // Prove existence of negative element
            assert(exists |k: int| 0 <= k < v.len() && v@[k] < 0) by {
                assert(0 <= (index as int) < v.len() && v@[(index as int)] < 0);
            };
            
            return (true, index as int);
        }
        index += 1;
    }
    
    // At this point, index == v.len() and all elements are non-negative
    assert(index == v.len());
    assert(forall |j: int| 0 <= j < v.len() ==> v@[j] >= 0) by {
        assert(forall |j: int| 0 <= j < index ==> v@[j] >= 0);
        assert(index == v.len());
    };
    
    // Prove that no negative element exists
    assert(!(exists |k: int| 0 <= k < v.len() && v@[k] < 0)) by {
        assert(forall |k: int| 0 <= k < v.len() ==> v@[k] >= 0);
    };
    
    return (false, 0);
}

}