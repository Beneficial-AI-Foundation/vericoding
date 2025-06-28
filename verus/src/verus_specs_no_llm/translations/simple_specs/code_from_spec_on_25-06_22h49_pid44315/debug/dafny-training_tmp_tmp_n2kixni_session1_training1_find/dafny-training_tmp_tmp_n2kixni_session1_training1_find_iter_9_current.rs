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
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key
        decreases a.len() - i
    {
        if a[i] == key {
            // Prove the postconditions for the found case
            assert(0 <= i < a.len());
            assert(a[i] == key);
            assert(forall|j: int| 0 <= j < i ==> a[j] != key) by {
                // This follows from the loop invariant
            };
            return i;
        }
        i = i + 1;
    }
    // At this point, we've checked all elements and none matched
    assert(i == a.len()) by {
        // Loop terminated because i >= a.len(), but invariant says i <= a.len()
    };
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] != key) by {
        // This follows from the loop invariant and the fact that i == a.len()
        assert(forall|j: int| 0 <= j < i ==> a[j] != key);
        assert(i == a.len());
    };
    return -1;
}

}