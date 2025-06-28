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
            assert(a.spec_index((i-1) as int) > a.spec_index(i as int));
            assert(!(a.spec_index((i-1) as int) <= a.spec_index(i as int)));
            assert(exists j : int :: 1 <= j < a.len() && !(a.spec_index(j-1) <= a.spec_index(j))) by {
                assert(1 <= i as int < a.len() && !(a.spec_index((i as int)-1) <= a.spec_index(i as int)));
            }
            return false;
        }
        i = i + 1;
    }
    
    assert(forall j : int :: 1 <= j < a.len() ==> a.spec_index(j-1) <= a.spec_index(j)) by {
        assert(i == a.len());
        assert(forall j : int :: 1 <= j < i ==> a.spec_index(j-1) <= a.spec_index(j));
    }
    
    return true;
}

}