use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn find(a: Seq<int>, key: int) -> (index: int)
    requires
        true
    ensures
        // If index is non-negative, it's a valid index and the element at that index equals key
        (index >= 0 ==> (0 <= index < a.len() && a[index] == key)) &&
        // If index is negative, the key is not in the sequence
        (index < 0 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key)) &&
        // If index is non-negative, it's the first occurrence of key
        (index >= 0 ==> (forall|i: int| 0 <= i < index ==> a[i] != key))
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key
    {
        if a[i as int] == key {
            return i as int;
        }
        i = i + 1;
    }
    return -1;
}

}