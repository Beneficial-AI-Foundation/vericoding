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
        assert(forall |k: int| 0 <= k < a.len() / 2 ==> k < i as int) by {
            // We exited the loop because i >= len / 2
            // Since i < len / 2 was false, we have i >= len / 2
            // For any k < a.len() / 2, since len == a.len(), we have k < len / 2
            // And since i >= len / 2, we have k < i
            assert(!(i < len / 2)); // Loop condition was false
            assert(len == a.len());
        }
        // From the loop invariant, for all k < i as int, we have matching pairs
        // Since all k < a.len() / 2 satisfy k < i as int, they all have matching pairs
    };
    
    return true;
}

}