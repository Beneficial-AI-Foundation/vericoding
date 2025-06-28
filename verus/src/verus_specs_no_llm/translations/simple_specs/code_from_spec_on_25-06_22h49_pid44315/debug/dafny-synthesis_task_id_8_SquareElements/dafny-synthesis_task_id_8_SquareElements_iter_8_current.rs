use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquareElements(a: Vec<int>) -> (squared: Vec<int>)
    requires
        forall|i: int| 0 <= i < a.len() ==> {
            let val = a.spec_index(i);
            val * val <= int::MAX && val * val >= int::MIN
        }
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
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i),
            forall|i: int| 0 <= i < a.len() ==> {
                let val = a.spec_index(i);
                val * val <= int::MAX && val * val >= int::MIN
            }
    {
        let element = a[index];
        proof {
            // Help Verus understand that the multiplication is safe
            assert(element == a.spec_index(index as int));
            assert(element * element <= int::MAX && element * element >= int::MIN);
        }
        let squared_element = element * element;
        result.push(squared_element);
        
        proof {
            // Help Verus understand the relationship after push
            assert(result.len() == index + 1);
            assert(result.spec_index(index as int) == squared_element);
            assert(result.spec_index(index as int) == a.spec_index(index as int) * a.spec_index(index as int));
            
            // Maintain the invariant for all previous elements
            assert(forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i)) by {
                // This follows from the loop invariant before the push operation
            };
        }
        
        index = index + 1;
    }
    
    proof {
        // After the loop, help Verus verify the postcondition
        assert(index == a.len());
        assert(result.len() == a.len());
        assert(forall|i: int| 0 <= i < a.len() ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i));
    }
    
    result
}

}