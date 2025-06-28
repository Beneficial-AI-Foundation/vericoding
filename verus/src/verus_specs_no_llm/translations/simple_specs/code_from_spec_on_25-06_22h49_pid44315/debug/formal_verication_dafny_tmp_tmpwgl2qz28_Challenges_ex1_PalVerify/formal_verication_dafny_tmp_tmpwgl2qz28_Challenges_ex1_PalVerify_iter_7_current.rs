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
            forall |k: int| 0 <= k < i as int ==> a.spec_index(k) == a.spec_index(len as int - k - 1),
            forall |j: int| 0 <= j < a.len() ==> a.spec_index(j) == old(a.spec_index(j)),
            len == a.len()
    {
        if a[i] != a[len - i - 1] {
            assert(a.spec_index(i as int) != a.spec_index(a.len() - (i as int) - 1));
            assert(0 <= i as int < a.len() / 2);
            return false;
        }
        i += 1;
    }
    
    // After the loop, we know all pairs match
    assert(i == len / 2);
    assert(len as int == a.len());
    
    // Key insight: prove that i covers all indices up to a.len()/2
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> k < i as int) by {
        // We know i == len / 2 and len == a.len()
        // For usize division: len / 2 = floor(len / 2)
        // For int division: a.len() / 2 = floor(a.len() / 2)  
        // Since len == a.len(), we have i as int == a.len() / 2
        // But we need to handle the case where a.len() is odd
        
        // Actually, let's use the fact that i >= len/2 in usize arithmetic
        // This means i * 2 >= len in usize arithmetic
        // Converting to int: (i as int) * 2 >= len as int = a.len()
        // So i as int >= a.len() / 2 
        
        // The key insight is that for any k < a.len()/2, 
        // we have k < floor(a.len()/2) <= i
        assert(i as int * 2 >= a.len()) by {
            // From i >= len/2 in usize arithmetic
            assert(i * 2 >= len || i * 2 + 1 == len);
            assert(len == a.len());
        }
    };
    
    // Now we can prove the main postcondition
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> 
        a.spec_index(k) == a.spec_index(a.len() - k - 1)) by {
        // From loop invariant and the fact that we covered all k < a.len()/2
        assert(forall |k: int| 0 <= k < i as int ==> 
            a.spec_index(k) == a.spec_index(len as int - k - 1));
        assert(len as int == a.len());
        assert(forall |k: int| 0 <= k < a.len() / 2 ==> k < i as int);
    };
    
    return true;
}

}