use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsGreater(n: int, a: Vec<int>) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> n > a.spec_index(i),
        !result ==> exists|i: int| 0 <= i < a.len() && n <= a.spec_index(i)
{
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> n > a.spec_index(j)
    {
        if n <= a[i] {
            return false;
        }
        i = i + 1;
    }
    
    return true;
}

}