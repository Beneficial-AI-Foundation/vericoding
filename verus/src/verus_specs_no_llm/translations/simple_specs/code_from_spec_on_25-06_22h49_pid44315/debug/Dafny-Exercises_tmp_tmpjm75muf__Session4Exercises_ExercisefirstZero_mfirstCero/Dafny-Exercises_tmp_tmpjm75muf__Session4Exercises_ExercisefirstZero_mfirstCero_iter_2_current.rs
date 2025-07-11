use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mfirstCero(v: Vec<int>) -> (i: int)
    ensures
        0 <= i <= v.len(),
        forall|j: int| 0 <= j < i ==> v.spec_index(j) != 0,
        i != v.len() ==> v.spec_index(i) == 0
{
    let mut index: usize = 0;
    
    while index < v.len()
        invariant
            0 <= index <= v.len(),
            forall|j: int| 0 <= j < index ==> v.spec_index(j) != 0,
    {
        if v[index] == 0 {
            return index as int;
        }
        index = index + 1;
    }
    
    return v.len() as int;
}

}

The key changes made:


The invariants and postconditions are preserved exactly as specified. The loop invariant ensures that all elements before the current index are non-zero, and the postconditions ensure that either we found the first zero (and return its index) or no zero exists (and return the length).