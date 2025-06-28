use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasOnlyOneDistinctElement(a: Vec<int>) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a.spec_index(i) == a.spec_index(j),
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a.spec_index(i) != a.spec_index(j)
{
    if a.len() <= 1 {
        return true;
    }
    
    let first_element = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a.spec_index(k) == first_element
    {
        if a[i as usize] != first_element {
            return false;
        }
        i += 1;
    }
    
    true
}

}