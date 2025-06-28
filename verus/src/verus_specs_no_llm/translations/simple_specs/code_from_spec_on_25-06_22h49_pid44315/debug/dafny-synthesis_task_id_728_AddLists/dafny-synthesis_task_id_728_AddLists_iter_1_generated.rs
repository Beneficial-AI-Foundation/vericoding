// Translated from Dafny
use builtin::*;
use builtin_macros::*;

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
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result.spec_index(i) == a.spec_index(i) + b.spec_index(i)
    {
        result = result.push(a.spec_index(idx) + b.spec_index(idx));
        idx = idx + 1;
    }
    
    result
}

}