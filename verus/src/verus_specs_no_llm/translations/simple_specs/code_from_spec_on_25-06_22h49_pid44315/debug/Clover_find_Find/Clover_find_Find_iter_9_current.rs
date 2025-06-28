use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Find(a: Vec<int>, key: int) -> (index: int)
    ensures
        -1 <= index < a.len(),
        index != -1 ==> a.spec_index(index) == key && (forall|i: int| 0 <= i < index ==> a.spec_index(i) != key),
        index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) != key)
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a.spec_index(j) != key
    {
        if a[i] == key {
            let result = i as int;
            assert(a.spec_index(result) == key);
            assert(0 <= result < a.len());
            assert(-1 <= result);
            assert(forall|j: int| 0 <= j < result ==> a.spec_index(j) != key);
            return result;
        }
        i = i + 1;
    }
    
    // When we exit the loop, we've checked all elements
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) != key);
    
    // For the bounds: -1 <= -1 < a.len()
    // We need to prove that a.len() > -1, which is always true since len() >= 0
    assert(-1 <= -1);
    assert(a.len() >= 0);
    assert(-1 < a.len() || a.len() == 0);
    if a.len() == 0 {
        assert(-1 < 0);
    } else {
        assert(-1 < a.len());
    }
    
    -1
}

}