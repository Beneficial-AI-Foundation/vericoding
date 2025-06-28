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
            // At this point, we found a mismatch at position i
            assert(str.as_bytes()@[i as int] != pre.as_bytes()@[i as int]);
            // This means the forall condition is false
            assert(!(forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@[j] == pre.as_bytes()@[j])) by {
                // We can show this by providing i as a counterexample
                assert(0 <= i < pre.len());
                assert(str.as_bytes()@[i as int] != pre.as_bytes()@[i as int]);
            }
            // Therefore false == !(forall...) which means false == (forall...) is false
            return false;
        }
        assert(str.as_bytes()@[i as int] == pre.as_bytes()@[i as int]);
        i = i + 1;
    }
    
    // When we exit the loop, i == pre.len()
    assert(i == pre.len());
    // The loop invariant gives us: forall|j: int| 0 <= j < i ==> str.as_bytes()@[j] == pre.as_bytes()@[j]
    // Since i == pre.len(), this becomes: forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@[j] == pre.as_bytes()@[j]
    assert(forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@[j] == pre.as_bytes()@[j]) by {
        // This follows directly from the loop invariant and i == pre.len()
        assert(forall|j: int| 0 <= j < i ==> str.as_bytes()@[j] == pre.as_bytes()@[j]);
        assert(i == pre.len());
    }
    return true;
}

}