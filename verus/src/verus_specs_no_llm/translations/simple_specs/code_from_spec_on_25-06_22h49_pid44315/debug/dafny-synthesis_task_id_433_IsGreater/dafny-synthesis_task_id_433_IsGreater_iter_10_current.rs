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
                // Help Verus understand that we found a witness for the existential
                let witness_index = i as int;
                assert(0 <= witness_index < a.len());
                assert(n <= a.spec_index(witness_index));
                // This establishes the existential quantifier
                assert(exists|k: int| 0 <= k < a.len() && n <= a.spec_index(k)) by {
                    assert(0 <= witness_index < a.len() && n <= a.spec_index(witness_index));
                }
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        // When we exit the loop, we've checked all elements
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < i ==> n > a.spec_index(j));
        // Since i == a.len(), this gives us the postcondition
        assert(forall|j: int| 0 <= j < a.len() ==> n > a.spec_index(j));
    }
    return true;
}

}