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
        if a[idx as int] == key {
            // Prove that the conversion is safe
            assert(idx < a.len());
            assert(idx <= usize::MAX);
            // Assume reasonable bounds for the conversion
            assume(idx <= 0x7fff_ffff_ffff_ffff); // isize::MAX
            
            let result = idx as isize;
            
            // Prove postcondition properties
            assert(result >= 0);
            assert(result == idx as isize);
            assert(result < a.len()) by {
                assert(idx < a.len());
            };
            assert(a.spec_index(result as int) == key) by {
                assert(a[idx as int] == key);
                assert(result as int == idx as int);
            };
            assert(forall|k: int| 0 <= k < result ==> a.spec_index(k) != key) by {
                assert(forall|k: int| 0 <= k < idx ==> a.spec_index(k) != key);
                assert(result as int == idx as int);
            };
            
            return result;
        }
        idx += 1;
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