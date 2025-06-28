use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Find(a: Vec<int>, key: int) -> (i: isize)
    ensures
        0 <= i ==> (// (1) i is smaller than the length of a
            i < a.len() && 
            // (2) key is at position i in a
            a.spec_index(i as int) == key && 
            // (3) i is the smallest position where key appears
            forall|k: int| 0 <= k < i ==> a.spec_index(k) != key
           ),
        i < 0 ==> 
      // a does not contain key
      forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) != key
{
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            forall|k: int| 0 <= k < idx ==> a.spec_index(k) != key,
        decreases a.len() - idx
    {
        if a[idx] == key {
            assert(a.spec_index(idx as int) == key);
            assert(forall|k: int| 0 <= k < idx ==> a.spec_index(k) != key);
            assert(0 <= idx < a.len());
            assert(idx as isize >= 0);
            assert((idx as isize) as int == idx as int);
            return idx as isize;
        }
        idx += 1;
    }
    
    assert(idx == a.len());
    assert(forall|k: int| 0 <= k < idx ==> a.spec_index(k) != key);
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) != key);
    return -1;
}

}