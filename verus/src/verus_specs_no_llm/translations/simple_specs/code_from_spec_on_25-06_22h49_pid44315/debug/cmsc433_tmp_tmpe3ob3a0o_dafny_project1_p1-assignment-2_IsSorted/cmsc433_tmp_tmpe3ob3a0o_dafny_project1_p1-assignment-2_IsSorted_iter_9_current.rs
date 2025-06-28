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
            // When we find a violation, we need to show that the sortedness property is false
            let j_int = i as int;
            assert(a[i-1] == a.spec_index(j_int-1));
            assert(a[i] == a.spec_index(j_int));
            assert(a.spec_index(j_int-1) > a.spec_index(j_int));
            assert(1 <= j_int < a.len());
            // This shows there exists a j where the sortedness condition fails
            return false;
        }
        i = i + 1;
    }
    
    // When we exit the loop, i == a.len(), so the invariant covers all valid indices
    assert(i == a.len());
    return true;
}

}