use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CubeElements(a: Vec<int>) -> (cubed: Vec<int>)
    ensures
        cubed.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> cubed.spec_index(i) == a.spec_index(i) * a.spec_index(i) * a.spec_index(i)
{
    let mut result = Vec::new();
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            result.len() == index,
            index <= a.len(),
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i) * a.spec_index(i)
    {
        let element = a[index];
        let cubed_element = element * element * element;
        result.push(cubed_element);
        
        proof {
            assert(result.len() == index + 1);
            assert(result.spec_index(index as int) == cubed_element);
            assert(cubed_element == a.spec_index(index as int) * a.spec_index(index as int) * a.spec_index(index as int));
            
            // Help the verifier understand the invariant is maintained
            assert forall|i: int| 0 <= i < (index + 1) implies result.spec_index(i) == a.spec_index(i) * a.spec_index(i) * a.spec_index(i) by {
                if i < index {
                    // This follows from the loop invariant
                } else {
                    assert(i == index);
                    assert(result.spec_index(i) == cubed_element);
                    assert(cubed_element == a.spec_index(i) * a.spec_index(i) * a.spec_index(i));
                }
            };
        }
        
        index = index + 1;
    }
    
    proof {
        assert(index == a.len());
        assert(result.len() == a.len());
        assert(forall|i: int| 0 <= i < a.len() ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i) * a.spec_index(i));
    }
    
    result
}

}