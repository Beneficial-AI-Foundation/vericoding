use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LucidNumbers(n: int) -> (lucid: Seq<int>)
    requires
        n >= 0
    ensures
        forall|i: int| 0 <= i < lucid.len() ==> lucid.spec_index(i) % 3 == 0,
        forall|i: int| 0 <= i < lucid.len() ==> lucid.spec_index(i) <= n,
        forall|i: int, j: int| 0 <= i < j < lucid.len() ==> lucid.spec_index(i) < lucid.spec_index(j)
{
    let mut result = Seq::empty();
    let mut current = 0int;
    
    while current <= n 
        invariant
            current >= 0,
            current % 3 == 0,
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) % 3 == 0,
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) < current,
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) <= n,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result.spec_index(i) < result.spec_index(j),
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == i * 3,
            result.len() == current / 3
        decreases n - current
    {
        result = result.push(current);
        current = current + 3;
        
        // Proof annotations to help verification
        assert(current >= 3);
        assert(current % 3 == 0);
        assert(result.len() == current / 3);
        assert(forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) % 3 == 0);
        assert(forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) < current);
        assert(forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) <= n);
        assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result.spec_index(i) < result.spec_index(j));
    }
    
    // Final assertions to ensure postconditions
    assert(forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) % 3 == 0);
    assert(forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) <= n);
    assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result.spec_index(i) < result.spec_index(j));
    
    result
}

}