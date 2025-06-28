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
    let len = a.len();
    
    while idx < len
        invariant
            0 <= idx <= len,
            len == a.len(),
            len == b.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result.spec_index(i) == a.spec_index(i) + b.spec_index(i)
    {
        proof {
            assert(idx < len);
            assert(idx < a.len());
            assert(idx < b.len());
        }
        result = result.push(a.spec_index(idx as int) + b.spec_index(idx as int));
        idx = idx + 1;
    }
    
    proof {
        assert(idx == len);
        assert(result.len() == len);
        assert(result.len() == a.len());
    }
    
    result
}

}