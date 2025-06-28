use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires
        0 < pre.len() <= str.len()
    ensures
        res == (forall|j: int| 0 <= j < pre.len() ==> 
            str@.index(j) == pre@.index(j))
{
    let mut i = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> str@.index(j) == pre@.index(j)
    {
        if str@.index(i as int) != pre@.index(i as int) {
            return false;
        }
        i = i + 1;
    }
    return true;
}

}