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
            str.as_bytes()@.index(j) == pre.as_bytes()@.index(j))
{
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            i <= str.len(),
            forall|j: int| 0 <= j < i ==> str.as_bytes()@.index(j) == pre.as_bytes()@.index(j)
        decreases pre.len() - i
    {
        if str.as_bytes()[i] != pre.as_bytes()[i] {
            assert(str.as_bytes()@.index(i as int) != pre.as_bytes()@.index(i as int));
            assert(!(forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@.index(j) == pre.as_bytes()@.index(j)));
            return false;
        }
        assert(str.as_bytes()@.index(i as int) == pre.as_bytes()@.index(i as int));
        i = i + 1;
    }
    
    // When we exit the loop, i == pre.len()
    assert(i == pre.len());
    // The loop invariant gives us: forall|j: int| 0 <= j < i ==> str.as_bytes()@.index(j) == pre.as_bytes()@.index(j)
    // Since i == pre.len(), this becomes: forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@.index(j) == pre.as_bytes()@.index(j)
    assert(forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@.index(j) == pre.as_bytes()@.index(j));
    return true;
}

}