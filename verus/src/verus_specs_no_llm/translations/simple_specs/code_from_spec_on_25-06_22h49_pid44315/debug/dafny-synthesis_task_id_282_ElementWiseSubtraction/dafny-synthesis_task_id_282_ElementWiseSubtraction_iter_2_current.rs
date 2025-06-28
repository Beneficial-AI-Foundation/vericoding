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
    let mut index = 0;
    
    while index < a.len()
        invariant
            index <= a.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) - b.spec_index(i)
    {
        let diff = a[index] - b[index];
        result.push(diff);
        index += 1;
        
        // Add proof assertion to help verification
        assert(result.len() == index);
        assert(result.spec_index(index - 1) == a.spec_index(index - 1) - b.spec_index(index - 1));
    }
    
    result
}

}