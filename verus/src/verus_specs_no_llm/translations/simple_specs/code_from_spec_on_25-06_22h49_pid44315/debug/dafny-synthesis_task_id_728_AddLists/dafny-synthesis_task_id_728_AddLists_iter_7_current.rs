use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AddLists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) + b.spec_index(i)
{
    let mut result = Seq::empty();
    let mut idx: usize = 0;
    let len = a.len() as usize;
    
    while idx < len
        invariant
            0 <= idx <= len,
            len == a.len(),
            len == b.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result.spec_index(i) == a.spec_index(i) + b.spec_index(i)
    {
        result = result.push(a.spec_index(idx as int) + b.spec_index(idx as int));
        idx = idx + 1;
    }
    
    result
}

}