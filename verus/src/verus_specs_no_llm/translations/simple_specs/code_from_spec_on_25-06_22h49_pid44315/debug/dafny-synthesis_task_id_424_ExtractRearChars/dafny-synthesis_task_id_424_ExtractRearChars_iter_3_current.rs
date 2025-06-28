use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ExtractRearChars(l: Seq<Seq<char>>) -> (r: Seq<char>)
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i].len() > 0
    ensures
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[i][l[i].len() - 1]
{
    let mut result = Seq::empty();
    let mut index: int = 0;
    
    while index < l.len()
        invariant
            0 <= index <= l.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] == l[i][l[i].len() - 1]
    {
        let current_string = l[index];
        assert(current_string.len() > 0); // From precondition
        let last_char = current_string[current_string.len() - 1];
        result = result.push(last_char);
        index = index + 1;
    }
    
    result
}

}