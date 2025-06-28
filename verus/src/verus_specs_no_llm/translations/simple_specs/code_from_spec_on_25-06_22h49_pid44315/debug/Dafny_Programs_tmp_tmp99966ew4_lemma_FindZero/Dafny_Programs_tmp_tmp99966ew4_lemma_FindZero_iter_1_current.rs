use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindZero(a: Vec<int>) -> (index: int)
    requires
        a.len() >= 0,
        forall|i: int| 0 <= i < a.len() ==> 0 <= a.spec_index(i),
        forall|i: int| 0 < i < a.len() ==> a.spec_index(i-1) - 1 <= a.spec_index(i)
    ensures
        index < 0 ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != 0,
        0 <= index ==> index < a.len() && a.spec_index(index) == 0
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) != 0
    {
        if a[i] == 0 {
            return i as int;
        }
        i = i + 1;
    }
    
    return -1;
}

}