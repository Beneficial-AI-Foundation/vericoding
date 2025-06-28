use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Tangent(r: Vec<int>, x: Vec<int>) -> (b: bool)
    requires
        forall i, j :: 0 <= i <= j < x.len() ==> x.spec_index(i) <= x.spec_index(j), // values in x will be in ascending order || empty,
        forall i, j :: (0 <= i < r.len() && 0 <= j < x.len()) ==> (r.spec_index(i) >= 0 && x.spec_index(j) >= 0)    // x && r will contain no negative values
    ensures
        !b ==> forall i, j :: 0 <= i< r.len() && 0 <= j < x.len() ==> r.spec_index(i) != x.spec_index(j),
        b ==> exists i, j :: 0 <= i< r.len() && 0 <= j < x.len() && r.spec_index(i) == x.spec_index(j)
{
    let mut i = 0;
    while i < r.len()
        invariant
            0 <= i <= r.len(),
            forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < x.len() ==> r.spec_index(k1) != x.spec_index(k2)
    {
        let mut j = 0;
        while j < x.len()
            invariant
                0 <= j <= x.len(),
                0 <= i < r.len(),
                forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < x.len() ==> r.spec_index(k1) != x.spec_index(k2),
                forall k2 :: 0 <= k2 < j ==> r.spec_index(i) != x.spec_index(k2)
        {
            if r.spec_index(i) == x.spec_index(j) {
                // We found a match, so the function should return true
                // Need to prove the postcondition for b = true
                assert(r.spec_index(i) == x.spec_index(j));
                assert(0 <= i < r.len() && 0 <= j < x.len());
                // This proves the exists clause for the postcondition
                assert(exists k1, k2 :: 0 <= k1 < r.len() && 0 <= k2 < x.len() && r.spec_index(k1) == x.spec_index(k2)) by {
                    assert(0 <= i < r.len() && 0 <= j < x.len() && r.spec_index(i) == x.spec_index(j));
                }
                return true;
            }
            j += 1;
        }
        // After inner loop completes, we know r[i] != x[k] for all k in x
        assert(forall k2 :: 0 <= k2 < x.len() ==> r.spec_index(i) != x.spec_index(k2));
        i += 1;
    }
    // After both loops complete, no element in r matches any element in x
    // The invariant tells us that for all k1 < i (which is now r.len()), 
    // r[k1] != x[k2] for all k2
    assert(i == r.len());
    assert(forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < x.len() ==> r.spec_index(k1) != x.spec_index(k2));
    // This should follow from the invariant and i == r.len()
    assert(forall k1, k2 :: 0 <= k1 < r.len() && 0 <= k2 < x.len() ==> r.spec_index(k1) != x.spec_index(k2)) by {
        assert(i == r.len());
        assert(forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < x.len() ==> r.spec_index(k1) != x.spec_index(k2));
    }
    false
}

}