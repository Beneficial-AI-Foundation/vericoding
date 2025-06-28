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
                    // Convert the usize inequality to int
                    assert((i as int) < (len / 2) as int);
                    // Key insight: (len / 2) as int <= (len as int) / 2 for integer division
                    // This is because usize division truncates, and so does int division
                    // So floor(len/2) when computed as usize equals floor(len/2) when computed as int
                    assert((len / 2) as int <= (len as int) / 2) by {
                        // This is a fundamental property: for non-negative n,
                        // (n / 2) converted from usize to int equals n as int / 2
                        // Both perform floor division
                        let n_int = len as int;
                        let half_usize = (len / 2) as int;
                        let half_int = n_int / 2;
                        // These are actually equal for truncating division
                        assert(half_usize == half_int) by {
                            // Verus understands this property of integer division
                        }
                    };
                    // Therefore: witness_k < (len / 2) as int <= (len as int) / 2
                    assert(witness_k < (len as int) / 2);
                };
                assert(a.spec_index(witness_k) != a.spec_index((len as int) - witness_k - 1)) by {
                    // Show that spec_index corresponds to array indexing
                    assert(witness_k == i as int);
                    assert(a.spec_index(witness_k) == a[i]);
                    assert((len as int) - witness_k - 1 == (len - i - 1) as int);
                    assert(a.spec_index((len as int) - witness_k - 1) == a[len - i - 1]);
                    // And we know a[i] != a[len - i - 1] from the if condition
                };
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all necessary pairs
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        // Loop invariant gives us: forall |j: int| 0 <= j < (i as int) ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)
        // Loop exit condition: i >= len / 2
        
        // We need to show that every j in [0, (len as int)/2) was covered by the loop
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (i as int)) by {
            // Since loop exited, we have i >= len / 2
            assert(i >= len / 2);
            assert((i as int) >= (len / 2) as int);
            
            // Show (len as int)/2 <= (len / 2) as int
            assert((len as int) / 2 <= (len / 2) as int) by {
                // For integer division with non-negative numbers:
                // floor(n/2) computed as int division equals floor(n/2) computed as usize division
                let n = len as int;
                assert(n / 2 == (len / 2) as int) by {
                    // This is a property Verus can verify about integer division
                };
            };
            
            // Therefore: j < (len as int)/2 <= (len / 2) as int <= (i as int)
            // So j < (i as int), meaning j was processed in the loop
        };
        
        // Now we can apply the loop invariant to get our result
    };
    
    true
}

fn TEST() -> (result: i32)
    ensures result == 0
{
    0
}

}