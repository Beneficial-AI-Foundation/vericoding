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
    
    // Prove that we've checked all necessary positions
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> k < i as int) by {
        // Key insight: i as int >= (len as int) / 2
        // For any k in [0, a.len()/2), we have k < (len as int) / 2
        // Since len == a.len(), we get k < i as int
        assert(i as int >= (len as int) / 2);
        
        // For usize division vs int division:
        // len / 2 (usize) is floor(len / 2)
        // (len as int) / 2 (int) is also floor(len / 2) 
        // So i as int >= (len as int) / 2 = a.len() / 2
        // But we need strict inequality for the range [0, a.len()/2)
        
        // Actually, we need to be more careful about the upper bound
        assert(i as int * 2 >= len as int);  // This follows from i >= len/2
    };
    
    // Alternative approach: directly prove the postcondition
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> 
        a.spec_index(k) == a.spec_index(a.len() - k - 1)) by {
        // For any k in the range, we checked it in the loop
        assert(forall |k: int| 0 <= k < i as int ==> 
            a.spec_index(k) == a.spec_index(len as int - k - 1));
        
        // Since i >= len/2 and len == a.len(), we have:
        // for any k < a.len()/2, we must have k < i
        assert(i as int * 2 >= a.len());
        
        // This means for any k < a.len()/2, we have k < i
        // Therefore the loop invariant covers all such k
    };
    
    return true;
}

}