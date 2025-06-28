// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Find(a: Vec<int>, key: int) -> (i: int)
    ensures
        0 <= i ==> (// (1) i is smaller than the length of a
            i < a.len() && 
            // (2) key is at position i in a
            a.spec_index(i) == key && 
            // (3) i is the smallest position where key appears
            forall|k: int| 0 <= k < i ==> a.spec_index(k) != key
           ),
        i < 0 ==> 
      // a does not contain key
      forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) != key
{
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            forall|k: int| 0 <= k < idx ==> a.spec_index(k) != key,
    {
        if a[idx] == key {
            return idx as int;
        }
        idx += 1;
    }
    
    return -1;
}

}