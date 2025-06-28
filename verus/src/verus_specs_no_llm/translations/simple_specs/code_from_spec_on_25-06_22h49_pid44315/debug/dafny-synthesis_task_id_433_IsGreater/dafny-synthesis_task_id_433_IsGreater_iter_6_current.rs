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
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> n > a.spec_index(j)
    {
        if n <= a[i] {
            proof {
                assert(0 <= i < a.len());
                assert(n <= a.spec_index(i as int));
                assert(exists|k: int| 0 <= k < a.len() && n <= a.spec_index(k) by {
                    let witness_k = i as int;
                    assert(0 <= witness_k < a.len());
                    assert(n <= a.spec_index(witness_k));
                });
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < i ==> n > a.spec_index(j));
        assert(forall|j: int| 0 <= j < a.len() ==> n > a.spec_index(j));
    }
    return true;
}

}