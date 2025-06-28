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
    let mut index: usize = 0;
    
    while index < s.len() as usize
        invariant
            result.len() == index as int,
            forall|i: int| 0 <= i < index as int ==> result.spec_index(i) == s.spec_index(i),
            index <= s.len() as usize
    {
        result = result.push(s[index as int]);
        index = index + 1;
    }
    
    result
}

}