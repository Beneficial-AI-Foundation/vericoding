use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: &str, str: &str) -> (res: bool)
    requires
        0 < pre.len() <= str.len()
    ensures
        res == (forall|j: int| 0 <= j < pre.len() ==> 
            str.as_bytes()@[j] == pre.as_bytes()@[j])
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            pre.len() <= str.len(),
            forall|j: int| 0 <= j < i ==> str.as_bytes()@[j] == pre.as_bytes()@[j]
        decreases pre.len() - i
    {
        // We know i < pre.len() from loop condition
        // We know pre.len() <= str.len() from precondition
        // Therefore i < str.len()
        assert(i < pre.len());
        assert(pre.len() <= str.len());
        assert(i < str.len());
        
        if str.as_bytes()[i] != pre.as_bytes()[i] {
            assert(str.as_bytes()@[i as int] != pre.as_bytes()@[i as int]);
            assert(exists|k: int| 0 <= k < pre.len() && str.as_bytes()@[k] != pre.as_bytes()@[k]) by {
                assert(0 <= i < pre.len());
                assert(str.as_bytes()@[i as int] != pre.as_bytes()@[i as int]);
            }
            assert(!(forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@[j] == pre.as_bytes()@[j]));
            return false;
        }
        assert(str.as_bytes()@[i as int] == pre.as_bytes()@[i as int]);
        i = i + 1;
    }
    
    // When we exit the loop, i == pre.len()
    assert(i == pre.len());
    // The loop invariant gives us: forall|j: int| 0 <= j < i ==> str.as_bytes()@[j] == pre.as_bytes()@[j]
    // Since i == pre.len(), this becomes: forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@[j] == pre.as_bytes()@[j]
    assert(forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@[j] == pre.as_bytes()@[j]);
    return true;
}

}