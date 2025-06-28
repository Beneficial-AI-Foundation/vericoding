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
            assert(v.spec_index(index as int) == 0);
            assert(0 <= index < v.len());
            return index as int;
        }
        index = index + 1;
    }
    
    assert(index == v.len());
    assert(forall|j: int| 0 <= j < v.len() ==> v.spec_index(j) != 0);
    assert(forall|j: int| 0 <= j < index ==> v.spec_index(j) != 0);
    return v.len() as int;
}

}