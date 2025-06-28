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
                    // Key insight: len / 2 <= (len as int) / 2
                    assert((len / 2) as int <= (len as int) / 2);
                    assert((i as int) < (len / 2) as int);
                };
                assert(a.spec_index(i as int) != a.spec_index((len as int) - (i as int) - 1));
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all pairs
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        // After the loop, i == len / 2 (since i < len / 2 is false and i <= len / 2 from invariant)
        assert(!(i < len / 2));
        assert(i <= len / 2);
        assert(i == len / 2);
        
        // From the invariant, we know all pairs up to i are equal
        assert(forall |j: int| 0 <= j < (i as int) ==> a.spec_index(j) == a.spec_index((len as int) - j - 1));
        
        // Key: show that (i as int) >= (len as int) / 2
        // This means we've checked all necessary pairs
        assert((i as int) >= (len as int) / 2) by {
            assert(i == len / 2);
            // For integer division: (len / 2) as int >= (len as int) / 2 when len % 2 == 0
            // and (len / 2) as int == (len as int) / 2 when len % 2 == 1
            // In both cases, (len / 2) as int * 2 >= len - 1
            if len % 2 == 0 {
                assert((len / 2) * 2 == len);
                assert((len / 2) as int * 2 == len as int);
                assert((len / 2) as int == (len as int) / 2);
            } else {
                assert((len / 2) * 2 + 1 == len);
                assert((len / 2) as int * 2 + 1 == len as int);
                assert((len / 2) as int == (len as int) / 2);
            }
        };
        
        // Therefore, for any j < (len as int) / 2, we have j < (i as int)
        // So the invariant covers all required indices
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (i as int));
    };
    
    true
}

fn TEST() -> (result: i32)
    ensures result == 0
{
    0
}

}