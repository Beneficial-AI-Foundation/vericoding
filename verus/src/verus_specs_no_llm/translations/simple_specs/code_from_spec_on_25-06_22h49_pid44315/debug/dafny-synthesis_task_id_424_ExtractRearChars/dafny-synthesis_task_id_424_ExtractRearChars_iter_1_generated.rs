// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ExtractRearChars(l: Seq<String>) -> (r: Seq<char>)
    requires
        forall i :: 0 <= i < l.len() ==> l.spec_index(i).len() > 0
    ensures
        r.len() == l.len(),
        forall i :: 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index(i)[l.spec_index(i).len() - 1]
{
    let mut result = Seq::empty();
    let mut index = 0;
    
    while index < l.len()
        invariant
            0 <= index <= l.len(),
            result.len() == index,
            forall i :: 0 <= i < index ==> result.spec_index(i) == l.spec_index(i)[l.spec_index(i).len() - 1]
    {
        let current_string = l.spec_index(index);
        let last_char = current_string[current_string.len() - 1];
        result = result.push(last_char);
        index = index + 1;
    }
    
    result
}

}