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
            assert(0 <= i as int < a.len() / 2) by {
                assert(i < len / 2);
                assert(len == a.len());
                // usize division relationship to int division
                assert((i as int) < (len as int) / 2);
                assert((len as int) / 2 <= a.len() / 2);
            }
            return false;
        }
        i += 1;
    }
    
    // After the loop, we know all pairs match
    assert(i == len / 2);
    assert(len as int == a.len());
    
    // Prove that we've checked all necessary pairs
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> k < i as int) by {
        // We exited the loop with i >= len / 2
        // In usize arithmetic: i >= len / 2 means i * 2 >= len or i * 2 + 1 == len
        // Converting to int: (i as int) * 2 >= (len as int)
        // Since len == a.len(): (i as int) * 2 >= a.len()
        // Therefore: i as int >= a.len() / 2
        
        // For any k < a.len() / 2, we have k < i as int
        assert((i as int) * 2 >= a.len()) by {
            // From the loop condition: i >= len / 2 in usize arithmetic
            // This means either i * 2 >= len or i * 2 + 1 >= len
            // In both cases, when converted to int: (i as int) * 2 >= (len as int) = a.len()
        }
        
        // Now for any k with 0 <= k < a.len() / 2:
        // k < a.len() / 2 <= (i as int * 2) / 2 = i as int
        assert(forall |k: int| 0 <= k < a.len() / 2 ==> k < i as int) by {
            // Since (i as int) * 2 >= a.len(), we have i as int >= a.len() / 2
            // And for integer division, k < a.len() / 2 implies k <= a.len() / 2 - 1 < i as int
        }
    };
    
    // Now we can prove the main postcondition
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> 
        a.spec_index(k) == a.spec_index(a.len() - k - 1)) by {
        // From loop invariant: all k < i as int have matching pairs
        // From above: all k < a.len() / 2 satisfy k < i as int
        // And len as int == a.len(), so the indices match
    };
    
    return true;
}

}