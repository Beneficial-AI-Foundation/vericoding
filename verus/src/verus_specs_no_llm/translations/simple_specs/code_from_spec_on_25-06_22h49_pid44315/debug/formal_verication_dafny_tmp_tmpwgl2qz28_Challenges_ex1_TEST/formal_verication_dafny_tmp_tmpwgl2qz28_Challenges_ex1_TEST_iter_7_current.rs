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
                let witness_k = i as int;
                assert(0 <= witness_k);
                assert(witness_k < (len as int) / 2) by {
                    assert(i < len / 2);
                    // Since i < len / 2 and both are usize, we have (i as int) < (len / 2) as int
                    assert((i as int) < (len / 2) as int);
                    // We need (len / 2) as int <= (len as int) / 2
                    // This follows from properties of integer division
                    assert((len / 2) as int <= (len as int) / 2) by {
                        let len_int = len as int;
                        let len_div_2 = len / 2;
                        // For non-negative integers: n/2 as usize converted to int <= n as int / 2
                        // This is a fundamental property of integer division
                    };
                };
                assert(a.spec_index(witness_k) != a.spec_index((len as int) - witness_k - 1)) by {
                    assert(a.spec_index(i as int) == a[i]);
                    assert(a.spec_index((len as int) - (i as int) - 1) == a[len - i - 1]);
                    assert(a[i] != a[len - i - 1]);
                };
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all necessary pairs
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        // Loop exit condition: !(i < len / 2), so i >= len / 2
        assert(!(i < len / 2));
        
        // For any j in the required range, show it was covered by the loop
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (i as int)) by {
            // Since i >= len / 2, we have (i as int) >= (len / 2) as int
            // And since (len as int)/2 <= (len / 2) as int, any j < (len as int)/2 satisfies j < (i as int)
            
            // Key property: (len as int) / 2 <= (len / 2) as int
            assert((len as int) / 2 <= (len / 2) as int) by {
                // This is true for integer division: floor(n/2) <= floor(n)/2 when converting back
                let n = len as int;
                let usize_div = len / 2;
                // The usize division len/2 gives us floor(len/2)
                // Converting to int preserves the value
                // And n/2 also gives us floor(n/2)
                // So they are equal, hence <= holds
            };
            
            // Since i >= len/2, we have (i as int) >= (len/2) as int >= (len as int)/2
            assert((len / 2) as int <= (i as int));
            assert((len as int) / 2 <= (len / 2) as int);
            
            // Therefore, for any j < (len as int)/2, we have j < (i as int)
        };
        
        // Apply the loop invariant to conclude
    };
    
    true
}

fn TEST() -> (result: i32)
    ensures result == 0
{
    0
}

}