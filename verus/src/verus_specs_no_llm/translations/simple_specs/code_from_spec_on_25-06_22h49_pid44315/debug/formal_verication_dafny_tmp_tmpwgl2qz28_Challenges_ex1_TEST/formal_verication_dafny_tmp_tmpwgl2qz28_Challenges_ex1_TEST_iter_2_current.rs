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
                assert(0 <= (i as int) < (len as int)/2) by {
                    assert(i < len / 2);
                    assert((len / 2) as int <= (len as int) / 2);
                };
                assert(a.spec_index(i as int) != a.spec_index((len as int) - (i as int) - 1));
            };
            return false;
        }
        i += 1;
    }
    
    assert(forall |j: int| 0 <= j < (len as int)/2 ==> a.spec_index(j) == a.spec_index((len as int) - j - 1)) by {
        assert(i == len / 2);
        assert((len / 2) as int <= (len as int) / 2);
        assert(forall |j: int| 0 <= j < (i as int) ==> a.spec_index(j) == a.spec_index((len as int) - j - 1));
        assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (i as int)) by {
            assert(forall |j: int| 0 <= j < (len as int)/2 ==> j < (len / 2) as int);
            assert((len / 2) as int == (i as int));
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