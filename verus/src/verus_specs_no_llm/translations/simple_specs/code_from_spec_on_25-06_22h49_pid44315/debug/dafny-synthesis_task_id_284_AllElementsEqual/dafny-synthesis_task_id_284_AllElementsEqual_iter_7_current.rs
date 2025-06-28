use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllElementsEqual(a: Vec<int>, n: int) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) == n,
        !result ==> exists|i: int| 0 <= i < a.len() && a.spec_index(i) != n
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) == n
    {
        if a[i] != n {
            return false;
        }
        i += 1;
    }
    
    return true;
}

}