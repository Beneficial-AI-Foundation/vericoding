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
                assert(0 <= witness_k < (len as int)/2);
                assert(a.spec_index(witness_k) != a.spec_index((len as int) - witness_k - 1));
            };
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all necessary pairs
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (i as int)) by {
            // Since i >= len/2 when loop exits, and (len as int)/2 <= len/2 as int
            assert((len as int)/2 <= len/2 as int);
            assert(len/2 as int <= i as int);
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