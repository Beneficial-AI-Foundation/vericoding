use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PalVerify(a: Vec<char>) -> (yn: bool)
    ensures
        yn == true ==> forall |i: int| 0 <= i < a.len()/2 ==> a.spec_index(i) == a.spec_index(a.len() - i - 1),
        yn == false ==> exists |i: int| 0 <= i < a.len()/2 && a.spec_index(i) != a.spec_index(a.len() - i - 1),
        forall |j: int| 0 <= j < a.len() ==> a.spec_index(j) == old(a.spec_index(j))
{
    let mut i: usize = 0;
    let len = a.len();
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall |k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(len as int - k - 1),
            forall |j: int| 0 <= j < a.len() ==> a.spec_index(j) == old(a.spec_index(j)),
            len == a.len()
    {
        if a[i] != a[len - i - 1] {
            // Establish the witness for the exists clause
            assert(i as int < len as int / 2);
            assert(len as int == a.len());
            assert(i as int < a.len() / 2);
            assert(a.spec_index(i as int) != a.spec_index(a.len() - (i as int) - 1));
            return false;
        }
        i += 1;
    }
    
    // After the loop, we know all pairs match
    assert(i == len / 2);
    assert(len as int == a.len());
    
    // Key insight: establish the relationship between usize and int division
    // When i == len / 2 (usize division), we have i as int <= len as int / 2
    // But we need to show that we've checked all positions up to a.len() / 2
    
    // For any k in the range [0, a.len()/2), either:
    // 1. k < i, so we checked it in the loop, or  
    // 2. k >= i, but since i == len/2 and len == a.len(), this is impossible
    
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> {
        // Since i as int >= len as int / 2 and len == a.len()
        // and integer division rounds down, we have k < i
        k < i as int
    }) by {
        // The key insight: if len is even, then len/2 (usize) == len/2 (int)
        // if len is odd, then len/2 (usize) == (len-1)/2 (int), but we still
        // need to check all positions up to len/2 (int division)
        assert(i as int >= (len as int) / 2);
        assert(len as int == a.len());
    };
    
    // Now we can conclude all pairs match
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> 
        a.spec_index(k) == a.spec_index(a.len() - k - 1));
    
    return true;
}

}