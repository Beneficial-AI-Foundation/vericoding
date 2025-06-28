use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSorted(a: Vec<int>) -> (isSorted: bool)
    ensures
        isSorted <==> forall j : int :: 1 <= j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j)
{
    if a.len() <= 1 {
        return true;
    }
    
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall j : int :: 1 <= j < i ==> a.spec_index(j-1) <= a.spec_index(j)
    {
        if a[i-1] > a[i] {
            assert(i >= 1);
            assert(i < a.len());
            assert(a[i-1] > a[i]);
            // Convert to int for spec_index
            let j_int = i as int;
            assert(a.spec_index(j_int-1) > a.spec_index(j_int));
            assert(!(a.spec_index(j_int-1) <= a.spec_index(j_int)));
            assert(1 <= j_int < a.len());
            assert(j_int - 1 >= 0);
            assert(exists j : int :: 1 <= j < a.len() && !(a.spec_index(j-1) <= a.spec_index(j))) by {
                let witness_j = j_int;
                assert(1 <= witness_j < a.len());
                assert(witness_j - 1 >= 0);
                assert(!(a.spec_index(witness_j-1) <= a.spec_index(witness_j)));
            }
            return false;
        }
        i = i + 1;
    }
    
    assert(forall j : int :: 1 <= j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j)) by {
        assert(i == a.len());
        assert(forall j : int :: 1 <= j < i ==> a.spec_index(j-1) <= a.spec_index(j));
        // The loop invariant already establishes this for all j < i
        // Since i == a.len(), this covers all valid j
    }
    
    return true;
}

}