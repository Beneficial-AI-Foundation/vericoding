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
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> 
        a.spec_index(k) == a.spec_index(a.len() - k - 1)) by {
        // We exited the loop because i >= len / 2
        assert(!(i < len / 2)); // Loop condition was false
        assert(len == a.len()); // From invariant
        
        // This means i >= len / 2, which means i as int >= (len / 2) as int
        // Since len == a.len(), we have i as int >= (a.len() / 2) as int
        assert(i as int >= (len / 2) as int);
        assert((len / 2) as int >= a.len() / 2 - 1); // Integer division property
        
        // For any k in range [0, a.len() / 2), we need to show k < i as int
        assert(forall |k: int| 0 <= k < a.len() / 2 ==> k < i as int) by {
            // Since a.len() / 2 is integer division, for any k < a.len() / 2,
            // we have k <= a.len() / 2 - 1
            // And since i as int >= (len / 2) as int and len == a.len(),
            // we can establish k < i as int
            assert(forall |k: int| 0 <= k < a.len() / 2 ==> k <= a.len() / 2 - 1);
            assert(i as int >= (a.len() / 2) as int);
            // The key insight: if i >= len/2 (usize division) and k < a.len()/2 (int division)
            // then k < i because the integer division rounds down
            assert(forall |k: int| k < a.len() / 2 ==> k < (a.len() / 2) as int + 1);
            assert((a.len() / 2) as int <= i as int);
        };
        
        // From the loop invariant, for all k < i as int, we have matching pairs
        assert(forall |k: int| 0 <= k < i as int ==> a.spec_index(k) == a.spec_index(len as int - k - 1));
        assert(len as int == a.len()); // len == a.len() and both convert to same int
        
        // Therefore, for all k in [0, a.len() / 2), we have matching pairs
        assert(forall |k: int| 0 <= k < a.len() / 2 ==> 
            a.spec_index(k) == a.spec_index(a.len() - k - 1));
    };
    
    return true;
}

}