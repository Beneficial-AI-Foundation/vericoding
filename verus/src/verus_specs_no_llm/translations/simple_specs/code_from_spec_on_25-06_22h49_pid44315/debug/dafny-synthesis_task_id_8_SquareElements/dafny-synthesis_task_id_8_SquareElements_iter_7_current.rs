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
        index = index + 1;
    }
    
    result
}

}