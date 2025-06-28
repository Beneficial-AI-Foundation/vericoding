use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllElementsEqual(a: Vec<int>, n: int) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) == n,
        !result ==> exists|i: int| 0 <= i < a.len() && a.spec_index(i) != n
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) == n
    {
        if a[i] != n {
            assert(a.spec_index(i as int) != n);
            assert(0 <= i < a.len());
            return false;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all elements
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) == n);
    
    return true;
}

}