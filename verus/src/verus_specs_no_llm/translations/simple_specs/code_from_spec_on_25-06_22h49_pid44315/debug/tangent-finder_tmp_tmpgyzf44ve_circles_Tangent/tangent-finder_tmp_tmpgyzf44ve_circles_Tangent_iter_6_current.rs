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
                // Prove the postcondition before returning
                assert(exists i_found, j_found :: 0 <= i_found < r.len() && 0 <= j_found < x.len() && r.spec_index(i_found) == x.spec_index(j_found)) by {
                    assert(0 <= i < r.len() && 0 <= j < x.len() && r.spec_index(i) == x.spec_index(j));
                }
                return true;
            }
            j += 1;
        }
        // After the inner loop, we know r[i] doesn't match any element in x
        assert(forall k2 :: 0 <= k2 < x.len() ==> r.spec_index(i) != x.spec_index(k2));
        i += 1;
    }
    
    // After both loops, we know no element in r matches any element in x
    assert(forall i_final, j_final :: 0 <= i_final < r.len() && 0 <= j_final < x.len() ==> r.spec_index(i_final) != x.spec_index(j_final)) by {
        assert(forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < x.len() ==> r.spec_index(k1) != x.spec_index(k2));
        assert(i == r.len());
    }
    false
}

}