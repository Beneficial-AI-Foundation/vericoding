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
            forall |k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(len - k - 1),
            forall |j: int| 0 <= j < a.len() ==> a.spec_index(j) == old(a.spec_index(j))
    {
        if a[i] != a[len - i - 1] {
            assert(a.spec_index(i as int) != a.spec_index(len - i as int - 1));
            assert(0 <= i < len / 2);
            return false;
        }
        i += 1;
    }
    
    assert(i == len / 2);
    assert(forall |k: int| 0 <= k < len / 2 ==> a.spec_index(k) == a.spec_index(len - k - 1));
    return true;
}

}