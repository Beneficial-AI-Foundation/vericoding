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
        index = index + 1;
    }
    
    result
}

}