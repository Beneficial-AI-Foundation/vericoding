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
        let squared_element = element * element;
        
        // Key insight: use the precise precondition for this specific index
        assert(element == a.spec_index(index as int));
        assert({
            let val = a.spec_index(index as int);
            val * val <= int::MAX && val * val >= int::MIN
        });
        assert(squared_element == element * element);
        assert(squared_element == a.spec_index(index as int) * a.spec_index(index as int));
        
        result.push(squared_element);
        
        // After push, verify the invariant is maintained
        assert(result.len() == index + 1);
        assert(result.spec_index(index as int) == squared_element);
        assert(result.spec_index(index as int) == a.spec_index(index as int) * a.spec_index(index as int));
        
        index = index + 1;
    }
    
    result
}

}