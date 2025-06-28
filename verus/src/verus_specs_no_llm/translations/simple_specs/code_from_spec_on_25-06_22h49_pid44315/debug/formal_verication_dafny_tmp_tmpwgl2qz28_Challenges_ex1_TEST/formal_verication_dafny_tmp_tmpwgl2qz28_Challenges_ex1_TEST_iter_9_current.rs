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
                    // Since i < len / 2 and we're dealing with non-negative integers
                    assert(i < len / 2);
                    // For the witness to work, we need i as int < (len as int) / 2
                    // This follows from i < len / 2 when len > 0
                };
                assert(a.spec_index(witness_k) != a.spec_index((len as int) - witness_k - 1)) by {
                    assert(witness_k == i as int);
                    assert(a.spec_index(witness_k) == a[i]);
                    assert(a.spec_index((len as int) - witness_k - 1) == a[len - i - 1]);
                };
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all necessary pairs
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        // The loop invariant tells us this property holds for all j < i
        // We need to show that when the loop exits, i covers all indices up to (len as int)/2
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (i as int)) by {
            // Loop exit condition means i >= len / 2
            // For any j < (len as int)/2, we have j < i
            // This is true because integer division properties ensure
            // (len as int)/2 <= (len/2 as int) <= i as int
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