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
    let mut index = 0;
    
    while index < a.len()
        invariant
            result.len() == index,
            index <= a.len(),
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == a.spec_index(i) * a.spec_index(i) * a.spec_index(i)
    {
        let cubed_element = a[index] * a[index] * a[index];
        result.push(cubed_element);
        index = index + 1;
    }
    
    result
}

}