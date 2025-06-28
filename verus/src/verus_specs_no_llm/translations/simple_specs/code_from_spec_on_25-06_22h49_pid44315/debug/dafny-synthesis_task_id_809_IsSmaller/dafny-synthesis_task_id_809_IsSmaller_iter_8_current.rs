use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSmaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires
        a.len() == b.len()
    ensures
        result == (forall i :: 0 <= i < a.len() ==> a.spec_index(i) > b.spec_index(i)),
        result == !(exists i :: 0 <= i < a.len() && a.spec_index(i) <= b.spec_index(i))
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall j :: 0 <= j < i ==> a.spec_index(j) > b.spec_index(j)
    {
        if a.spec_index(i as int) <= b.spec_index(i as int) {
            // We found an element where a[i] <= b[i]
            // This proves the existence part for !result
            assert(exists k :: 0 <= k < a.len() && a.spec_index(k) <= b.spec_index(k)) by {
                assert(0 <= i < a.len());
                assert(a.spec_index(i as int) <= b.spec_index(i as int));
            };
            // This proves that the forall condition is false
            assert(!(forall j :: 0 <= j < a.len() ==> a.spec_index(j) > b.spec_index(j))) by {
                assert(0 <= i < a.len());
                assert(a.spec_index(i as int) <= b.spec_index(i as int));
                assert(!(a.spec_index(i as int) > b.spec_index(i as int)));
            };
            return false;
        }
        i = i + 1;
    }
    
    // When we exit the loop, we've checked all elements and all satisfy a[j] > b[j]
    assert(forall j :: 0 <= j < a.len() ==> a.spec_index(j) > b.spec_index(j)) by {
        assert(i == a.len());
        // The loop invariant tells us: forall j :: 0 <= j < i ==> a.spec_index(j) > b.spec_index(j)
        // Since i == a.len(), this means: forall j :: 0 <= j < a.len() ==> a.spec_index(j) > b.spec_index(j)
    };
    
    // This proves that the exists condition is false when result is true
    assert(!(exists k :: 0 <= k < a.len() && a.spec_index(k) <= b.spec_index(k))) by {
        // By contradiction: if there exists such k, then a.spec_index(k) <= b.spec_index(k)
        // But we proved forall j :: 0 <= j < a.len() ==> a.spec_index(j) > b.spec_index(j)
        // This would mean a.spec_index(k) > b.spec_index(k), which contradicts a.spec_index(k) <= b.spec_index(k)
    };
    
    return true;
}

}