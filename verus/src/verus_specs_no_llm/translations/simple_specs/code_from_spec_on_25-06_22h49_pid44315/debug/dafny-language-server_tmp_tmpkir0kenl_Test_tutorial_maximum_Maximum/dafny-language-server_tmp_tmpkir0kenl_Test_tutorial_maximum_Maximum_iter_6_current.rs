use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Maximum(values: Seq<int>) -> (max: int)
    requires
        values != Seq::<int>::empty(),
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values.spec_index(i) <= max
{
    let mut max = values.spec_index(0);
    let mut i: usize = 1;
    
    while i < values.len()
        invariant
            0 < i <= values.len(),
            values.contains(max),
            forall|j: int| 0 <= j < i ==> values.spec_index(j) <= max
        decreases values.len() - i
    {
        if values.spec_index(i as int) > max {
            max = values.spec_index(i as int);
        }
        i = i + 1;
        
        // Proof assertions to help verification
        assert(values.contains(max));
        assert(forall|j: int| 0 <= j < i ==> values.spec_index(j) <= max);
    }
    
    // Final assertion to ensure postcondition
    assert(i == values.len());
    assert(forall|j: int| 0 <= j < values.len() ==> values.spec_index(j) <= max);
    
    max
}

}