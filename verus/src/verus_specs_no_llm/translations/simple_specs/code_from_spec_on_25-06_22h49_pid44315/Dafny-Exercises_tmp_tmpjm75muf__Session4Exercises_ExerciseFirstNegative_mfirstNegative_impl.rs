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
            positive(v@.subrange(0, index as int)),
    {
        if v[index] < 0 {
            // Found a negative element
            assert(v@[index as int] < 0);
            assert(0 <= index < v.len());
            assert(positive(v@.subrange(0, index as int)));
            return (true, index as int);
        }
        index += 1;
    }
    
    // At this point, we've checked all elements and none are negative
    assert(index == v.len());
    assert(positive(v@.subrange(0, v.len() as int)));
    
    // The subrange from 0 to v.len() is the entire sequence
    assert(v@.subrange(0, v.len() as int) =~= v@);
    assert(positive(v@));
    
    // Since positive(v@) means all elements are >= 0, no element can be < 0
    assert(forall |k: int| 0 <= k < v.len() ==> v@[k] >= 0);
    
    // This proves that the existential is false
    assert(!(exists |k: int| 0 <= k < v.len() && v@[k] < 0)) by {
        if exists |k: int| 0 <= k < v.len() && v@[k] < 0 {
            let witness_k = choose |k: int| 0 <= k < v.len() && v@[k] < 0;
            assert(0 <= witness_k < v.len() && v@[witness_k] < 0);
            assert(v@[witness_k] >= 0); // from the forall above
            assert(false); // contradiction
        }
    }
    
    (false, 0)
}

}