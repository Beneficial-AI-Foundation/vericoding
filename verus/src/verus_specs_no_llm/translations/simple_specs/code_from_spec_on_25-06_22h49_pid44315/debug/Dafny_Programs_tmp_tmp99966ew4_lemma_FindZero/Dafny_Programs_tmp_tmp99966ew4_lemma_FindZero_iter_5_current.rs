use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindZero(a: Vec<int>) -> (index: int)
    requires
        a.len() >= 0,
        forall|i: int| 0 <= i < a.len() ==> 0 <= a.spec_index(i),
        forall|i: int| 0 < i < a.len() ==> a.spec_index(i-1) - 1 <= a.spec_index(i)
    ensures
        index < 0 ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != 0,
        0 <= index ==> index < a.len() && a.spec_index(index) == 0
{
    let mut i: int = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) != 0
    {
        if a[i as usize] == 0 {
            assert(a.spec_index(i) == 0);
            assert(0 <= i < a.len());
            return i;
        }
        assert(a.spec_index(i) != 0);
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) != 0);
    return -1;
}

}