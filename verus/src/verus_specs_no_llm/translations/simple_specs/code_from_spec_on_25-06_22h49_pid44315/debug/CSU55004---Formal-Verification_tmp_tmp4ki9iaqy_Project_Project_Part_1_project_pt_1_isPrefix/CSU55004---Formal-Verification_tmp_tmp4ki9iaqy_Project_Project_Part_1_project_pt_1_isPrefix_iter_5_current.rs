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
    {
        if str.as_bytes()[i] != pre.as_bytes()[i] {
            assert(str.as_bytes()@.index(i as int) != pre.as_bytes()@.index(i as int));
            return false;
        }
        assert(str.as_bytes()@.index(i as int) == pre.as_bytes()@.index(i as int));
        i = i + 1;
    }
    assert(forall|j: int| 0 <= j < pre.len() ==> str.as_bytes()@.index(j) == pre.as_bytes()@.index(j));
    return true;
}

}