// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseDivide(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b.spec_index(i) != 0
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) / b.spec_index(i)
{
    let mut result = Seq::empty();
    let mut index = 0;
    
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            result.len() == index,
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) / b.spec_index(i)
    {
        let div_result = a.spec_index(index) / b.spec_index(index);
        result = result.push(div_result);
        index = index + 1;
    }
    
    result
}

}