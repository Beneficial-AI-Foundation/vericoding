use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsGreater(n: int, a: Vec<int>) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> n > a.spec_index(i),
        !result ==> exists|i: int| 0 <= i < a.len() && n <= a.spec_index(i)
{
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> n > a.spec_index(j)
    {
        if n <= a[i] {
            // Proof: we found an index i where n <= a[i], and 0 <= i < a.len()
            assert(0 <= i < a.len() && n <= a.spec_index(i as int));
            return false;
        }
        i = i + 1;
    }
    
    // Proof: we've checked all indices and n > a[j] for all 0 <= j < a.len()
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> n > a.spec_index(j));
    return true;
}

}