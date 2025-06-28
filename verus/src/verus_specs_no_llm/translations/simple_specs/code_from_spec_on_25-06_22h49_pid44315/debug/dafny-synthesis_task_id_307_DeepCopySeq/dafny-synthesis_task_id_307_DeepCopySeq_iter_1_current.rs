use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DeepCopySeq(s: Seq<int>) -> (copy: Seq<int>)
    ensures
        copy.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> copy.spec_index(i) == s.spec_index(i)
{
    let mut result: Seq<int> = Seq::empty();
    let mut index: usize = 0;
    
    while index < s.len()
        invariant
            result.len() == index,
            forall i :: 0 <= i < index ==> result.spec_index(i) == s.spec_index(i)
    {
        result = result.push(s.spec_index(index as int));
        index = index + 1;
    }
    
    result
}

}