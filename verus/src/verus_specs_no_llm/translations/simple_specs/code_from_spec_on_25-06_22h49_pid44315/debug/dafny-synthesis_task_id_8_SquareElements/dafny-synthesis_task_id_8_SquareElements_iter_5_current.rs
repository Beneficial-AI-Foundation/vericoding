use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquareElements(a: Vec<int>) -> (squared: Vec<int>)
    ensures
        squared.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> squared.spec_index(i) == a.spec_index(i) * a.spec_index(i)
{
    let mut result = Vec::new();
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            result.len() == index,
            index <= a.len(),
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i)
    {
        let element = a[index];
        let squared_element = element * element;
        result.push(squared_element);
        
        // Store the old index for the proof
        let old_index = index;
        index = index + 1;
        
        // Proof assertion to help establish the invariant after the increment
        assert(forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i)) by {
            // The result now has length index (which is old_index + 1)
            assert(result.len() == index);
            
            // For all previous elements, the invariant still holds
            assert(forall|i: int| 0 <= i < old_index ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i));
            
            // For the newly added element at position old_index
            assert(result.spec_index(old_index as int) == squared_element);
            assert(squared_element == element * element);
            assert(element == a.spec_index(old_index as int));
            assert(result.spec_index(old_index as int) == a.spec_index(old_index as int) * a.spec_index(old_index as int));
        };
    }
    
    result
}

}