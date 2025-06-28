use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DeepCopySeq(s: Seq<int>) -> (copy: Seq<int>)
    ensures
        copy.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> copy.spec_index(i) == s.spec_index(i)
{
    let mut result: Seq<int> = Seq::empty();
    let mut index: int = 0;
    
    while index < s.len()
        invariant
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result.spec_index(i) == s.spec_index(i),
            index >= 0
    {
        result = result.push(s.spec_index(index));
        index = index + 1;
    }
    
    result
}

}