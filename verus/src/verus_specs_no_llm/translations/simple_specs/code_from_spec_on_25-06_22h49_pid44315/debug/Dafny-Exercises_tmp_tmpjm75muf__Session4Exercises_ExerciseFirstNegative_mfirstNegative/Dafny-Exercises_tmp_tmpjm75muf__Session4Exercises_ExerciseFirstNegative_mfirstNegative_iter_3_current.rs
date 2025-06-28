use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u| 0 <= u < s.len() ==> s.spec_index(u) >= 0
}

fn firstNegative(v: Vec<int>) -> (b: bool, i: int)
    ensures
        b <==> exists |k| 0 <= k < v.len() && v.spec_index(k) < 0,
        b ==> 0 <= i < v.len() && v.spec_index(i) < 0 && positive(v@.subrange(0, i as int))
{
    let mut index = 0;
    
    while index < v.len()
        invariant
            0 <= index <= v.len(),
            forall |j| 0 <= j < index ==> v.spec_index(j) >= 0,
    {
        if v[index] < 0 {
            // Prove that the prefix is positive
            assert(forall |j| 0 <= j < index ==> v.spec_index(j) >= 0);
            
            // Help Verus understand the subrange relationship
            assert(forall |u| 0 <= u < (index as int) ==> 
                v@.subrange(0, index as int).spec_index(u) == v@.spec_index(u));
            
            // Now prove positive holds for the subrange
            assert(forall |u| 0 <= u < v@.subrange(0, index as int).len() ==> 
                v@.subrange(0, index as int).spec_index(u) >= 0) by {
                assert(forall |u| 0 <= u < (index as int) ==> 
                    v@.subrange(0, index as int).spec_index(u) == v@.spec_index(u) >= 0);
            };
            
            assert(positive(v@.subrange(0, index as int)));
            
            // Prove existence of negative element
            assert(v.spec_index(index) < 0);
            assert(exists |k| 0 <= k < v.len() && v.spec_index(k) < 0) by {
                assert(0 <= index < v.len() && v.spec_index(index) < 0);
            };
            
            return (true, index as int);
        }
        index += 1;
    }
    
    // Prove that no negative element exists
    assert(forall |j| 0 <= j < v.len() ==> v.spec_index(j) >= 0);
    assert(!(exists |k| 0 <= k < v.len() && v.spec_index(k) < 0)) by {
        if exists |k| 0 <= k < v.len() && v.spec_index(k) < 0 {
            let k = choose |k| 0 <= k < v.len() && v.spec_index(k) < 0;
            assert(v.spec_index(k) >= 0); // Contradiction
        }
    };
    
    return (false, 0);
}

}