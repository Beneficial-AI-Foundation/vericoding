use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseSubtraction(a: Vec<int>, b: Vec<int>) -> (result: Vec<int>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) - b.spec_index(i)
{
    let mut result = Vec::new();
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            index <= a.len(),
            result.len() == index,
            a.len() == b.len(),
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) - b.spec_index(i)
    {
        let diff = a.spec_index(index as int) - b.spec_index(index as int);
        result.push(diff);
        
        // Proof assertions to help Verus verify the loop invariant
        assert(result.len() == index + 1);
        assert(result.spec_index(index as int) == diff);
        assert(diff == a.spec_index(index as int) - b.spec_index(index as int));
        
        index += 1;
    }
    
    // Final assertion to help with the postcondition
    assert(index == a.len());
    assert(result.len() == a.len());
    
    result
}

}