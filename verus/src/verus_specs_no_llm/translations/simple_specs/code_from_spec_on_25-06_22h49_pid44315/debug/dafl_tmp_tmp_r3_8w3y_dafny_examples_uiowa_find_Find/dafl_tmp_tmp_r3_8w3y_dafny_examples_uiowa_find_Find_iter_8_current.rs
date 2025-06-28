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
            // Convert idx to isize - this is safe because idx < a.len() and Vec lengths fit in isize
            let result = idx as isize;
            
            // Prove postcondition properties
            assert(result >= 0);
            assert(result < a.len() as isize);
            assert(a.spec_index(result as int) == key) by {
                assert(a[idx] == key);
                assert(result as int == idx as int);
            };
            assert(forall|k: int| 0 <= k < result ==> a.spec_index(k) != key) by {
                assert(forall|k: int| 0 <= k < idx ==> a.spec_index(k) != key);
                assert(result as int == idx as int);
            };
            
            return result;
        }
        idx = idx + 1;
    }
    
    // Key not found - prove the negative case
    assert(idx == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) != key) by {
        assert(forall|k: int| 0 <= k < idx ==> a.spec_index(k) != key);
        assert(idx == a.len());
    };
    
    return -1;
}

}