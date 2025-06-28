use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn strictNegative(v: &Vec<int>, i: int, j: int) -> bool {
    forall|u: int| i <= u < j ==> v@[u] < 0
}

spec fn isPermutation(s: Seq<int>, t: Seq<int>) -> bool {
    s.to_multiset() == t.to_multiset()
}

fn separate(v: &mut Vec<int>) -> (i: usize)
    ensures 
        i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strictNegative(v, i as int, v.len() as int),
        isPermutation(v@, old(v)@)
{
    let mut left = 0;
    let mut right = 0;
    let ghost old_v = v@;
    
    while right < v.len()
        invariant
            left <= right <= v.len(),
            positive(v@.subrange(0, left as int)),
            forall|k: int| left <= k < right ==> v@[k] < 0,
            isPermutation(v@, old_v)
    {
        if v[right] >= 0 {
            // Swap v[left] and v[right]
            let temp = v[left];
            v.set(left, v[right]);
            v.set(right, temp);
            
            left += 1;
        }
        right += 1;
    }
    
    // Final assertions to help verification
    assert(left <= v.len());
    assert(positive(v@.subrange(0, left as int)));
    assert(forall|k: int| left <= k < v.len() ==> v@[k] < 0) by {
        assert(right == v.len());
        assert(forall|k: int| left <= k < right ==> v@[k] < 0);
    }
    assert(strictNegative(v, left as int, v.len() as int));
    assert(isPermutation(v@, old_v));
    
    left
}

}