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
                    assert(i < len / 2);
                    assert((i as int) < (len / 2) as int);
                    // For integer division: (len / 2) as int <= (len as int) / 2
                    assert((len / 2) as int <= (len as int) / 2);
                };
                assert(a.spec_index(i as int) != a.spec_index((len as int) - (i as int) - 1));
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, i >= len / 2, so we've checked all necessary pairs
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        // From the loop invariant, we know:
        // forall |j: int| 0 <= j < (i as int) ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)
        
        // Since we exited the loop with !(i < len / 2), we have i >= len / 2
        // This means (i as int) >= (len / 2) as int
        
        // For any j where 0 <= j < (len as int)/2:
        // We need to show that j < (i as int) to use the invariant
        
        assert(!(i < len / 2));  // loop exit condition
        assert((len / 2) as int <= (i as int));  // convert to int
        
        // Key insight: for any integer j < (len as int)/2, we have j < (i as int)
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (i as int)) by {
            // If j < (len as int)/2, then j < (len / 2) as int <= (i as int)
            // We need to establish that (len as int)/2 <= (len / 2) as int
            // This is true because integer division truncates
            assert((len as int) / 2 <= (len / 2) as int) by {
                // This is a property of integer division
                let len_int = len as int;
                let len_div_2_usize = len / 2;
                let len_div_2_int = len_int / 2;
                // len_div_2_int <= len_div_2_usize as int
            };
        };
        
        // Now we can apply the invariant
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> {
            &&& j < (i as int)  // from above
            &&& a.spec_index(j) == a.spec_index((len as int) - j - 1)  // from invariant
        });
    };
    
    true
}

fn TEST() -> (result: i32)
    ensures result == 0
{
    0
}

}