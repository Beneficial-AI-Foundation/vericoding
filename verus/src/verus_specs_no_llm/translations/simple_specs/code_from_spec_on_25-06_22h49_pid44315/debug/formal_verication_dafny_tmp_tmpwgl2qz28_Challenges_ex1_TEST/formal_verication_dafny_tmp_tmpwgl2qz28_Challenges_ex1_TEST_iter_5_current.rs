use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn PalVerify(a: Vec<char>) -> (yn: bool)
    requires a.len() < usize::MAX
    ensures 
        yn == true ==> forall |i: int| 0 <= i < (a.len() as int)/2 ==> a.spec_index(i) == a.spec_index((a.len() as int) - i - 1),
        yn == false ==> exists |i: int| 0 <= i < (a.len() as int)/2 && a.spec_index(i) != a.spec_index((a.len() as int) - i - 1)
{
    let len = a.len();
    if len == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < len / 2
        invariant 
            i <= len / 2,
            forall |j: int| 0 <= j < (i as int) ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)
    {
        if a[i] != a[len - i - 1] {
            assert(exists |k: int| 0 <= k < (len as int)/2 && a.spec_index(k) != a.spec_index((len as int) - k - 1)) by {
                assert(0 <= (i as int));
                assert((i as int) < (len as int) / 2) by {
                    // Since i < len / 2, we have i as int < (len / 2) as int
                    assert(i < len / 2);
                    // And (len / 2) as int <= (len as int) / 2 always holds
                    assert((i as int) < (len / 2) as int);
                    assert((len / 2) as int <= (len as int) / 2);
                };
                assert(a.spec_index(i as int) != a.spec_index((len as int) - (i as int) - 1));
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all pairs
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        // Use the fact that any j < (len as int) / 2 must be < i
        // because we've exited the loop where i < len / 2 was false
        
        // The key insight: if j < (len as int) / 2, then j must be representable as usize
        // and j < len / 2, so j < i (since we exited the loop)
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> {
            // j < (len as int) / 2 < len, so j fits in usize
            &&& j < len as int
            &&& j < (i as int)
        }) by {
            assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < len as int);
            assert(forall |j: int| 0 <= j < (len as int)/2 ==> {
                // Since j < (len as int) / 2 and j is integer
                // If j were >= i, then since j < len, we'd have j < len / 2
                // But we exited the loop with i >= len / 2, contradiction
                let j_usize = j as usize;
                j_usize < len / 2 ==> j_usize < i
            }) by {
                // This follows from the loop termination condition
                assert(!(i < len / 2));
                assert(i <= len / 2);  // from invariant
            };
        };
    };
    
    true
}

fn TEST() -> (result: i32)
    ensures result == 0
{
    0
}

}