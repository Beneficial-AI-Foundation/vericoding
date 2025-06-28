use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Find(a: Vec<int>, key: int) -> (index: int)
    ensures
        -1<=index<a.len(),
        index!=-1 ==> a.spec_index(index)==key && (forall|i| 0 <= i < index ==> a.spec_index(i) != key),
        index == -1 ==> (forall|i| 0 <= i < a.len() ==> a.spec_index(i) != key)
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) != key
    {
        if a[i] == key {
            assert(i < a.len());
            assert(i as int >= 0);
            assert(i as int < a.len());
            assert(a.spec_index(i as int) == key);
            return i as int;
        }
        i = i + 1;
    }
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) != key);
    return -1;
}

}