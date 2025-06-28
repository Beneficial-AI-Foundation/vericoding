use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn buscar(a: Vec<int>, x: int) -> (r: int)
    ensures
        r < 0 ==> forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != x,
        0 <= r < a.len() ==> a.spec_index(r) == x
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            forall|j: int| 0 <= j < i as int ==> a.spec_index(j) != x,
            i <= a.len()
    {
        if a[i] == x {
            assert(a.spec_index(i as int) == x);
            assert(0 <= i as int < a.len());
            return i as int;
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < i as int ==> a.spec_index(j) != x);
    assert(i as int == a.len());
    return -1;
}

}