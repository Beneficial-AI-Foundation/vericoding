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
            forall |k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(len as int - k - 1),
            forall |j: int| 0 <= j < a.len() ==> a.spec_index(j) == old(a.spec_index(j))
    {
        if a[i] != a[len - i - 1] {
            assert(a.spec_index(i as int) != a.spec_index((len - i - 1) as int));
            assert(0 <= i < len / 2);
            assert(i as int < a.len() / 2);
            assert((len - i - 1) as int == a.len() - (i as int) - 1);
            assert(exists |k: int| 0 <= k < a.len()/2 && a.spec_index(k) != a.spec_index(a.len() - k - 1)) by {
                assert(0 <= i as int < a.len()/2);
                assert(a.spec_index(i as int) != a.spec_index(a.len() - (i as int) - 1));
            }
            return false;
        }
        i += 1;
    }
    
    assert(i == len / 2);
    assert(i as int == len as int / 2);
    assert(forall |k: int| 0 <= k < a.len() / 2 ==> a.spec_index(k) == a.spec_index(a.len() - k - 1)) by {
        assert(forall |k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(len as int - k - 1));
        assert(i as int == len as int / 2);
        assert(len as int == a.len());
    }
    return true;
}

}