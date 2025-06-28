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
            // Prove that we found the key at position i
            assert(a[i] == key);
            assert(a.spec_index(i as int) == key);
            // Prove the bounds
            assert(i < a.len());
            assert(0 <= i as int < a.len());
            assert(-1 <= i as int < a.len());
            // The loop invariant already proves that all elements before i are not key
            assert(forall|j: int| 0 <= j < i as int ==> a.spec_index(j) != key);
            return i as int;
        }
        i = i + 1;
    }
    // When we exit the loop, i == a.len()
    assert(i == a.len());
    // The loop invariant tells us that forall j: 0 <= j < i, a[j] != key
    // Since i == a.len(), this means forall j: 0 <= j < a.len(), a[j] != key
    assert(forall|j: int| 0 <= j < a.len() as int ==> a.spec_index(j) != key);
    // Prove the bounds for return value -1
    assert(-1 <= -1 < a.len());
    return -1;
}

}